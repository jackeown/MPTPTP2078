%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wb2jugKsE5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 404 expanded)
%              Number of leaves         :   26 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  833 (3458 expanded)
%              Number of equality atoms :   42 ( 193 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) )
       => ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
       != ( k1_wellord2 @ X21 ) )
      | ( ( k3_relat_1 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X21 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
        = X21 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_wellord2 @ X21 ) )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X22 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('26',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X21 ) )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ ( k1_wellord2 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ~ ( r2_hidden @ X23 @ X21 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ ( k1_wellord2 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ~ ( r2_hidden @ X23 @ X21 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X17 @ X18 ) @ ( sk_C @ X17 @ X18 ) ) @ X17 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X17 @ X18 ) @ ( sk_C @ X17 @ X18 ) ) @ X17 )
      | ( r1_tarski @ ( k6_relat_1 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('54',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k1_wellord2 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wb2jugKsE5
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 203 iterations in 0.129s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.59  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(t33_wellord2, conjecture,
% 0.38/0.59    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t73_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( ![C:$i]:
% 0.38/0.59           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.38/0.59         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_C @ X17 @ X18) @ X18)
% 0.38/0.59          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.38/0.59          | ~ (v1_relat_1 @ X17))),
% 0.38/0.59      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.59  thf(t25_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( v1_relat_1 @ B ) =>
% 0.38/0.59           ( ( r1_tarski @ A @ B ) =>
% 0.38/0.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.38/0.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X13)
% 0.38/0.59          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.38/0.59          | ~ (r1_tarski @ X14 @ X13)
% 0.38/0.59          | ~ (v1_relat_1 @ X14))),
% 0.38/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.59          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ (k1_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf(fc3_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.59  thf('4', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.59  thf(t71_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.59  thf('5', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.38/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.59          | (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.59  thf(d1_wellord2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.38/0.59         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.59           ( ![C:$i,D:$i]:
% 0.38/0.59             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.38/0.59               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.38/0.59                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         (((X22) != (k1_wellord2 @ X21))
% 0.38/0.59          | ((k3_relat_1 @ X22) = (X21))
% 0.38/0.59          | ~ (v1_relat_1 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X21 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ (k1_wellord2 @ X21))
% 0.38/0.59          | ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.59  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.38/0.59  thf('10', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.59  thf('11', plain, (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.38/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf(d6_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ( k3_relat_1 @ A ) =
% 0.38/0.59         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X11 : $i]:
% 0.38/0.59         (((k3_relat_1 @ X11)
% 0.38/0.59            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.38/0.59          | ~ (v1_relat_1 @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.38/0.59  thf(t7_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['11', '14'])).
% 0.38/0.59  thf('16', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.38/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X0 : $i, X2 : $i]:
% 0.38/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.59          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.59          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['7', '19'])).
% 0.38/0.59  thf('21', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.59          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.59         (((X22) != (k1_wellord2 @ X21))
% 0.38/0.59          | ~ (r2_hidden @ X23 @ X21)
% 0.38/0.59          | ~ (r2_hidden @ X24 @ X21)
% 0.38/0.59          | (r2_hidden @ (k4_tarski @ X23 @ X24) @ X22)
% 0.38/0.59          | ~ (r1_tarski @ X23 @ X24)
% 0.38/0.59          | ~ (v1_relat_1 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ (k1_wellord2 @ X21))
% 0.38/0.59          | ~ (r1_tarski @ X23 @ X24)
% 0.38/0.59          | (r2_hidden @ (k4_tarski @ X23 @ X24) @ (k1_wellord2 @ X21))
% 0.38/0.59          | ~ (r2_hidden @ X24 @ X21)
% 0.38/0.59          | ~ (r2_hidden @ X23 @ X21))),
% 0.38/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.59  thf('27', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X23 @ X24)
% 0.41/0.59          | (r2_hidden @ (k4_tarski @ X23 @ X24) @ (k1_wellord2 @ X21))
% 0.41/0.59          | ~ (r2_hidden @ X24 @ X21)
% 0.41/0.59          | ~ (r2_hidden @ X23 @ X21))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ X1)
% 0.41/0.59          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '28'])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | (r2_hidden @ 
% 0.41/0.59             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.41/0.59              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.41/0.59             (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['22', '30'])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (~ (r2_hidden @ 
% 0.41/0.59             (k4_tarski @ (sk_C @ X17 @ X18) @ (sk_C @ X17 @ X18)) @ X17)
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.41/0.59          | ~ (v1_relat_1 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.59  thf('34', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X13)
% 0.41/0.59          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.41/0.59          | ~ (r1_tarski @ X14 @ X13)
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.59          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.41/0.59             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.59  thf('39', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.59  thf('40', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('43', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf(t21_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( r1_tarski @
% 0.41/0.59         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X12 : $i]:
% 0.41/0.59         ((r1_tarski @ X12 @ 
% 0.41/0.59           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.41/0.59          | ~ (v1_relat_1 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.41/0.59           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('46', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.41/0.59          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.41/0.59      inference('demod', [status(thm)], ['45', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         ((r2_hidden @ (sk_C @ X17 @ X18) @ X18)
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.41/0.59          | ~ (v1_relat_1 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X0) @ X1)
% 0.41/0.59          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.41/0.59             (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (~ (r2_hidden @ 
% 0.41/0.59             (k4_tarski @ (sk_C @ X17 @ X18) @ (sk_C @ X17 @ X18)) @ X17)
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X18) @ X17)
% 0.41/0.59          | ~ (v1_relat_1 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.59  thf('53', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('54', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.41/0.59          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['55'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X13)
% 0.41/0.59          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.41/0.59          | ~ (r1_tarski @ X14 @ X13)
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.59          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.41/0.59             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.59  thf('59', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.59  thf('60', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.59  thf('61', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (![X0 : $i]: (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.41/0.59  thf(t12_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.59  thf('64', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59           = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.59  thf('65', plain, (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.41/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      (![X11 : $i]:
% 0.41/0.59         (((k3_relat_1 @ X11)
% 0.41/0.59            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.41/0.59          | ~ (v1_relat_1 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (![X0 : $i, X2 : $i]:
% 0.41/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.59          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ((k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.41/0.59              = (k1_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['66', '69'])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ 
% 0.41/0.59              (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59              = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['65', '70'])).
% 0.41/0.59  thf('72', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59          | ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ 
% 0.41/0.59              (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.41/0.59              = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.41/0.59  thf('74', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.59  thf('76', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('77', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('78', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) = (X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.41/0.59  thf('79', plain, (![X0 : $i]: ((k2_relat_1 @ (k1_wellord2 @ X0)) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['64', '78'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['47', '79'])).
% 0.41/0.59  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
