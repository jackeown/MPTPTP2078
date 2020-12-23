%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7tLda9U3xB

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 149 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  714 (1629 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t83_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
        & ! [F: $i,G: $i,H: $i,I: $i] :
            ~ ( ( r2_hidden @ F @ B )
              & ( r2_hidden @ G @ C )
              & ( r2_hidden @ H @ D )
              & ( r2_hidden @ I @ E )
              & ( A
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
          & ! [F: $i,G: $i,H: $i,I: $i] :
              ~ ( ( r2_hidden @ F @ B )
                & ( r2_hidden @ G @ C )
                & ( r2_hidden @ H @ D )
                & ( r2_hidden @ I @ E )
                & ( A
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) )
    | ( ( k1_mcart_1 @ sk_A )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k3_mcart_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_B )
      | ~ ( r2_hidden @ X22 @ sk_C )
      | ~ ( r2_hidden @ X23 @ sk_D )
      | ( sk_A
       != ( k4_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ( sk_A
       != ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('43',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k3_zfmisc_1 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E ) ),
    inference('sup-',[status(thm)],['6','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_E ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7tLda9U3xB
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 69 iterations in 0.035s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(t83_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.21/0.51          ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.21/0.51                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.21/0.51                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 0.21/0.51             ( ![F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.51               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 0.21/0.51                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 0.21/0.51                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t23_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.51         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 0.21/0.51          | ~ (v1_relat_1 @ X20)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.21/0.51        | ((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(d4_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X12 @ X13 @ X14) @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf(fc6_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (v1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X12 @ X13 @ X14) @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf(t10_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.51         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 0.21/0.51          | ~ (v1_relat_1 @ X20)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))
% 0.21/0.51        | ((k1_mcart_1 @ sk_A)
% 0.21/0.51            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51               (k2_mcart_1 @ (k1_mcart_1 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(d3_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((k1_mcart_1 @ sk_A)
% 0.21/0.51         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51            (k2_mcart_1 @ (k1_mcart_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf(d3_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51           (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X0)
% 0.21/0.51           = (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 0.21/0.51          | ~ (v1_relat_1 @ X20)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.21/0.51        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_A))
% 0.21/0.51            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((k1_mcart_1 @ (k1_mcart_1 @ sk_A))
% 0.21/0.51         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.21/0.51           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf(d4_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.51           = (k4_tarski @ (k3_mcart_1 @ X8 @ X9 @ X10) @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.51           = (k3_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X1 @ X0)
% 0.21/0.51           = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['28', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X21 @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ X22 @ sk_C)
% 0.21/0.51          | ~ (r2_hidden @ X23 @ sk_D)
% 0.21/0.51          | ((sk_A) != (k4_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.51          | ((sk_A)
% 0.21/0.51              != (k4_mcart_1 @ 
% 0.21/0.51                  (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ X2 @ 
% 0.21/0.51                  X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.51          | ~ (r2_hidden @ X2 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((sk_A)
% 0.21/0.51            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ 
% 0.21/0.51               sk_C)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A))) @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((sk_A)
% 0.21/0.51            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_A)) @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.51          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k3_zfmisc_1 @ sk_B @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_A)) @ sk_D)),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.51           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X12 @ X13 @ X14) @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '56'])).
% 0.21/0.51  thf('58', plain, (((sk_A) != (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['52', '57'])).
% 0.21/0.51  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
