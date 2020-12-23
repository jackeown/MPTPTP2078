%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J1vmSBnRIm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:33 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 210 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          : 1102 (1911 expanded)
%              Number of equality atoms :   61 ( 117 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X37 @ X38 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

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

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('16',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
       != ( k1_wellord2 @ X53 ) )
      | ( ( k3_relat_1 @ X54 )
        = X53 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('17',plain,(
    ! [X53: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X53 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X53 ) )
        = X53 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('18',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X53: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X53 ) )
      = X53 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('20',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X45 @ X46 ) @ ( sk_D_1 @ X45 @ X46 ) ) @ X46 )
      | ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X50 @ X51 ) @ X52 )
      | ( r2_hidden @ X50 @ ( k3_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X53: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X53 ) )
      = X53 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X45 @ X46 ) @ ( sk_D_1 @ X45 @ X46 ) ) @ X46 )
      | ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('39',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X50 @ X51 ) @ X52 )
      | ( r2_hidden @ X51 @ ( k3_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X45 @ X46 ) @ ( sk_D_1 @ X45 @ X46 ) ) @ X45 )
      | ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('61',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( X54
       != ( k1_wellord2 @ X53 ) )
      | ~ ( r2_hidden @ X55 @ X53 )
      | ~ ( r2_hidden @ X56 @ X53 )
      | ( r2_hidden @ ( k4_tarski @ X55 @ X56 ) @ X54 )
      | ~ ( r1_tarski @ X55 @ X56 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('62',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X53 ) )
      | ~ ( r1_tarski @ X55 @ X56 )
      | ( r2_hidden @ ( k4_tarski @ X55 @ X56 ) @ ( k1_wellord2 @ X53 ) )
      | ~ ( r2_hidden @ X56 @ X53 )
      | ~ ( r2_hidden @ X55 @ X53 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X55 @ X56 )
      | ( r2_hidden @ ( k4_tarski @ X55 @ X56 ) @ ( k1_wellord2 @ X53 ) )
      | ~ ( r2_hidden @ X56 @ X53 )
      | ~ ( r2_hidden @ X55 @ X53 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('69',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r2_hidden @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( k4_tarski @ X0 @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ ( k4_tarski @ X0 @ X0 ) @ ( k4_tarski @ X0 @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('73',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X43 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('76',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r2_hidden @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X37 @ X38 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X2 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X2 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','88'])).

thf('90',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J1vmSBnRIm
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 1148 iterations in 0.574s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/1.02  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.80/1.02  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.80/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.80/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/1.02  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.80/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.80/1.02  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.80/1.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/1.02  thf(t32_wellord2, conjecture,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.80/1.02       ( k1_tarski @ ( k4_tarski @ A @ A ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i]:
% 0.80/1.02        ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.80/1.02          ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t32_wellord2])).
% 0.80/1.02  thf('0', plain,
% 0.80/1.02      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.80/1.02         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t69_enumset1, axiom,
% 0.80/1.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.80/1.02  thf('1', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.02  thf(t36_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.80/1.02         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.80/1.02       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.80/1.02         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k2_tarski @ X38 @ X39))
% 0.80/1.02           = (k2_tarski @ (k4_tarski @ X37 @ X38) @ (k4_tarski @ X37 @ X39)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.80/1.02  thf('3', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.80/1.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['1', '2'])).
% 0.80/1.02  thf('4', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.02  thf('5', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.80/1.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf('6', plain,
% 0.80/1.02      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.80/1.02         != (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['0', '5'])).
% 0.80/1.02  thf('7', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.80/1.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf(d10_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.80/1.02  thf('8', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.80/1.02      inference('simplify', [status(thm)], ['8'])).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.02  thf(t38_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.80/1.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.80/1.02         ((r2_hidden @ X41 @ X42)
% 0.80/1.02          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.80/1.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['9', '12'])).
% 0.80/1.02  thf('14', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.80/1.02          (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['7', '13'])).
% 0.80/1.02  thf(d1_enumset1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.02       ( ![E:$i]:
% 0.80/1.02         ( ( r2_hidden @ E @ D ) <=>
% 0.80/1.02           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_1, axiom,
% 0.80/1.02    (![E:$i,C:$i,B:$i,A:$i]:
% 0.80/1.02     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.80/1.02       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.80/1.02  thf('15', plain,
% 0.80/1.02      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.02         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.80/1.02          | ((X4) = (X5))
% 0.80/1.02          | ((X4) = (X6))
% 0.80/1.02          | ((X4) = (X7)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.80/1.02  thf(d1_wellord2, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( v1_relat_1 @ B ) =>
% 0.80/1.02       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.80/1.02         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.80/1.02           ( ![C:$i,D:$i]:
% 0.80/1.02             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.80/1.02               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.80/1.02                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (![X53 : $i, X54 : $i]:
% 0.80/1.02         (((X54) != (k1_wellord2 @ X53))
% 0.80/1.02          | ((k3_relat_1 @ X54) = (X53))
% 0.80/1.02          | ~ (v1_relat_1 @ X54))),
% 0.80/1.02      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      (![X53 : $i]:
% 0.80/1.02         (~ (v1_relat_1 @ (k1_wellord2 @ X53))
% 0.80/1.02          | ((k3_relat_1 @ (k1_wellord2 @ X53)) = (X53)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['16'])).
% 0.80/1.02  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.80/1.02  thf('18', plain, (![X57 : $i]: (v1_relat_1 @ (k1_wellord2 @ X57))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.80/1.02  thf('19', plain, (![X53 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X53)) = (X53))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '18'])).
% 0.80/1.02  thf(d3_relat_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( v1_relat_1 @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( r1_tarski @ A @ B ) <=>
% 0.80/1.02           ( ![C:$i,D:$i]:
% 0.80/1.02             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.80/1.02               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.80/1.02  thf('20', plain,
% 0.80/1.02      (![X45 : $i, X46 : $i]:
% 0.80/1.02         ((r2_hidden @ 
% 0.80/1.02           (k4_tarski @ (sk_C @ X45 @ X46) @ (sk_D_1 @ X45 @ X46)) @ X46)
% 0.80/1.02          | (r1_tarski @ X46 @ X45)
% 0.80/1.02          | ~ (v1_relat_1 @ X46))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.80/1.02  thf(t30_relat_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( v1_relat_1 @ C ) =>
% 0.80/1.02       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.80/1.02         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.80/1.02           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.80/1.02  thf('21', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (~ (r2_hidden @ (k4_tarski @ X50 @ X51) @ X52)
% 0.80/1.02          | (r2_hidden @ X50 @ (k3_relat_1 @ X52))
% 0.80/1.02          | ~ (v1_relat_1 @ X52))),
% 0.80/1.02      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.80/1.02  thf('22', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_relat_1 @ X0)
% 0.80/1.02          | (r1_tarski @ X0 @ X1)
% 0.80/1.02          | ~ (v1_relat_1 @ X0)
% 0.80/1.02          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.02  thf('23', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.80/1.02          | (r1_tarski @ X0 @ X1)
% 0.80/1.02          | ~ (v1_relat_1 @ X0))),
% 0.80/1.02      inference('simplify', [status(thm)], ['22'])).
% 0.80/1.02  thf('24', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.80/1.02          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.80/1.02          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['19', '23'])).
% 0.80/1.02  thf('25', plain, (![X57 : $i]: (v1_relat_1 @ (k1_wellord2 @ X57))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.80/1.02  thf('26', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.80/1.02          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.80/1.02      inference('demod', [status(thm)], ['24', '25'])).
% 0.80/1.02  thf(t70_enumset1, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.80/1.02  thf('27', plain,
% 0.80/1.02      (![X16 : $i, X17 : $i]:
% 0.80/1.02         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.80/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.80/1.02  thf('28', plain,
% 0.80/1.02      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['27', '28'])).
% 0.80/1.02  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.80/1.02  thf(zf_stmt_3, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.02       ( ![E:$i]:
% 0.80/1.02         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.80/1.02  thf('30', plain,
% 0.80/1.02      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.80/1.02         (~ (r2_hidden @ X13 @ X12)
% 0.80/1.02          | ~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.80/1.02          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.80/1.02  thf('31', plain,
% 0.80/1.02      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.80/1.02         (~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.80/1.02          | ~ (r2_hidden @ X13 @ (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['30'])).
% 0.80/1.02  thf('32', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.80/1.02          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['29', '31'])).
% 0.80/1.02  thf('33', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.02          | ~ (zip_tseitin_0 @ 
% 0.80/1.02               (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0 @ X0 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['26', '32'])).
% 0.80/1.02  thf('34', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.02          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.02          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.02          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['15', '33'])).
% 0.80/1.02  thf('35', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.02          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['34'])).
% 0.80/1.02  thf('36', plain,
% 0.80/1.02      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.02         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.80/1.02          | ((X4) = (X5))
% 0.80/1.02          | ((X4) = (X6))
% 0.80/1.02          | ((X4) = (X7)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.80/1.02  thf('37', plain, (![X53 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X53)) = (X53))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '18'])).
% 0.80/1.02  thf('38', plain,
% 0.80/1.02      (![X45 : $i, X46 : $i]:
% 0.80/1.02         ((r2_hidden @ 
% 0.80/1.02           (k4_tarski @ (sk_C @ X45 @ X46) @ (sk_D_1 @ X45 @ X46)) @ X46)
% 0.80/1.02          | (r1_tarski @ X46 @ X45)
% 0.80/1.02          | ~ (v1_relat_1 @ X46))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (~ (r2_hidden @ (k4_tarski @ X50 @ X51) @ X52)
% 0.80/1.02          | (r2_hidden @ X51 @ (k3_relat_1 @ X52))
% 0.80/1.02          | ~ (v1_relat_1 @ X52))),
% 0.80/1.02      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_relat_1 @ X0)
% 0.80/1.02          | (r1_tarski @ X0 @ X1)
% 0.80/1.02          | ~ (v1_relat_1 @ X0)
% 0.80/1.02          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['38', '39'])).
% 0.80/1.02  thf('41', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.80/1.02          | (r1_tarski @ X0 @ X1)
% 0.80/1.02          | ~ (v1_relat_1 @ X0))),
% 0.80/1.02      inference('simplify', [status(thm)], ['40'])).
% 0.80/1.02  thf('42', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.80/1.02          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.80/1.02          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['37', '41'])).
% 0.80/1.03  thf('43', plain, (![X57 : $i]: (v1_relat_1 @ (k1_wellord2 @ X57))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.80/1.03  thf('44', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['42', '43'])).
% 0.80/1.03  thf('45', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.80/1.03          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['29', '31'])).
% 0.80/1.03  thf('46', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | ~ (zip_tseitin_0 @ 
% 0.80/1.03               (sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.80/1.03  thf('47', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.03          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.03          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['36', '46'])).
% 0.80/1.03  thf('48', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['47'])).
% 0.80/1.03  thf('49', plain,
% 0.80/1.03      (![X45 : $i, X46 : $i]:
% 0.80/1.03         (~ (r2_hidden @ 
% 0.80/1.03             (k4_tarski @ (sk_C @ X45 @ X46) @ (sk_D_1 @ X45 @ X46)) @ X45)
% 0.80/1.03          | (r1_tarski @ X46 @ X45)
% 0.80/1.03          | ~ (v1_relat_1 @ X46))),
% 0.80/1.03      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.80/1.03  thf('50', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ 
% 0.80/1.03             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.80/1.03             X1)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.03  thf('51', plain, (![X57 : $i]: (v1_relat_1 @ (k1_wellord2 @ X57))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.80/1.03  thf('52', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ 
% 0.80/1.03             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.80/1.03             X1)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['50', '51'])).
% 0.80/1.03  thf('53', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | ~ (r2_hidden @ 
% 0.80/1.03               (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.80/1.03               X1))),
% 0.80/1.03      inference('simplify', [status(thm)], ['52'])).
% 0.80/1.03  thf('54', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['35', '53'])).
% 0.80/1.03  thf('55', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.80/1.03          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.80/1.03      inference('simplify', [status(thm)], ['54'])).
% 0.80/1.03  thf('56', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.80/1.03          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['14', '55'])).
% 0.80/1.03  thf('57', plain,
% 0.80/1.03      (![X0 : $i, X2 : $i]:
% 0.80/1.03         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.03  thf('58', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 0.80/1.03             (k1_wellord2 @ (k1_tarski @ X0)))
% 0.80/1.03          | ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.80/1.03              = (k1_wellord2 @ (k1_tarski @ X0))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.80/1.03  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['9', '12'])).
% 0.80/1.03  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.80/1.03      inference('simplify', [status(thm)], ['8'])).
% 0.80/1.03  thf('61', plain,
% 0.80/1.03      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.80/1.03         (((X54) != (k1_wellord2 @ X53))
% 0.80/1.03          | ~ (r2_hidden @ X55 @ X53)
% 0.80/1.03          | ~ (r2_hidden @ X56 @ X53)
% 0.80/1.03          | (r2_hidden @ (k4_tarski @ X55 @ X56) @ X54)
% 0.80/1.03          | ~ (r1_tarski @ X55 @ X56)
% 0.80/1.03          | ~ (v1_relat_1 @ X54))),
% 0.80/1.03      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.80/1.03  thf('62', plain,
% 0.80/1.03      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ (k1_wellord2 @ X53))
% 0.80/1.03          | ~ (r1_tarski @ X55 @ X56)
% 0.80/1.03          | (r2_hidden @ (k4_tarski @ X55 @ X56) @ (k1_wellord2 @ X53))
% 0.80/1.03          | ~ (r2_hidden @ X56 @ X53)
% 0.80/1.03          | ~ (r2_hidden @ X55 @ X53))),
% 0.80/1.03      inference('simplify', [status(thm)], ['61'])).
% 0.80/1.03  thf('63', plain, (![X57 : $i]: (v1_relat_1 @ (k1_wellord2 @ X57))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.80/1.03  thf('64', plain,
% 0.80/1.03      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.80/1.03         (~ (r1_tarski @ X55 @ X56)
% 0.80/1.03          | (r2_hidden @ (k4_tarski @ X55 @ X56) @ (k1_wellord2 @ X53))
% 0.80/1.03          | ~ (r2_hidden @ X56 @ X53)
% 0.80/1.03          | ~ (r2_hidden @ X55 @ X53))),
% 0.80/1.03      inference('demod', [status(thm)], ['62', '63'])).
% 0.80/1.03  thf('65', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X0 @ X1)
% 0.80/1.03          | ~ (r2_hidden @ X0 @ X1)
% 0.80/1.03          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['60', '64'])).
% 0.80/1.03  thf('66', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.80/1.03          | ~ (r2_hidden @ X0 @ X1))),
% 0.80/1.03      inference('simplify', [status(thm)], ['65'])).
% 0.80/1.03  thf('67', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['59', '66'])).
% 0.80/1.03  thf('68', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['59', '66'])).
% 0.80/1.03  thf('69', plain,
% 0.80/1.03      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.80/1.03         ((r1_tarski @ (k2_tarski @ X41 @ X43) @ X44)
% 0.80/1.03          | ~ (r2_hidden @ X43 @ X44)
% 0.80/1.03          | ~ (r2_hidden @ X41 @ X44))),
% 0.80/1.03      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.80/1.03  thf('70', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 0.80/1.03          | (r1_tarski @ (k2_tarski @ X1 @ (k4_tarski @ X0 @ X0)) @ 
% 0.80/1.03             (k1_wellord2 @ (k1_tarski @ X0))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['68', '69'])).
% 0.80/1.03  thf('71', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (r1_tarski @ 
% 0.80/1.03          (k2_tarski @ (k4_tarski @ X0 @ X0) @ (k4_tarski @ X0 @ X0)) @ 
% 0.80/1.03          (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['67', '70'])).
% 0.80/1.03  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.80/1.03      inference('simplify', [status(thm)], ['8'])).
% 0.80/1.03  thf('73', plain,
% 0.80/1.03      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.80/1.03         ((r2_hidden @ X43 @ X42)
% 0.80/1.03          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.80/1.03      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.80/1.03  thf('74', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['72', '73'])).
% 0.80/1.03  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.80/1.03      inference('simplify', [status(thm)], ['8'])).
% 0.80/1.03  thf('76', plain,
% 0.80/1.03      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.80/1.03         ((r2_hidden @ X41 @ X42)
% 0.80/1.03          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.80/1.03      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.80/1.03  thf('77', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['75', '76'])).
% 0.80/1.03  thf('78', plain,
% 0.80/1.03      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.80/1.03         ((r1_tarski @ (k2_tarski @ X41 @ X43) @ X44)
% 0.80/1.03          | ~ (r2_hidden @ X43 @ X44)
% 0.80/1.03          | ~ (r2_hidden @ X41 @ X44))),
% 0.80/1.03      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.80/1.03  thf('79', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.80/1.03          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.80/1.03  thf('80', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['74', '79'])).
% 0.80/1.03  thf('81', plain,
% 0.80/1.03      (![X0 : $i, X2 : $i]:
% 0.80/1.03         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.03  thf('82', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.80/1.03          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.80/1.03  thf('83', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['74', '79'])).
% 0.80/1.03  thf('84', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['82', '83'])).
% 0.80/1.03  thf('85', plain,
% 0.80/1.03      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.80/1.03         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k2_tarski @ X38 @ X39))
% 0.80/1.03           = (k2_tarski @ (k4_tarski @ X37 @ X38) @ (k4_tarski @ X37 @ X39)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.80/1.03  thf('86', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X2))
% 0.80/1.03           = (k2_tarski @ (k4_tarski @ X1 @ X2) @ (k4_tarski @ X1 @ X0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['84', '85'])).
% 0.80/1.03  thf('87', plain,
% 0.80/1.03      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.03  thf('88', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 0.80/1.03          (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('demod', [status(thm)], ['71', '86', '87'])).
% 0.80/1.03  thf('89', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.80/1.03           = (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('demod', [status(thm)], ['58', '88'])).
% 0.80/1.03  thf('90', plain,
% 0.80/1.03      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.80/1.03         != (k1_wellord2 @ (k1_tarski @ sk_A)))),
% 0.80/1.03      inference('demod', [status(thm)], ['6', '89'])).
% 0.80/1.03  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
