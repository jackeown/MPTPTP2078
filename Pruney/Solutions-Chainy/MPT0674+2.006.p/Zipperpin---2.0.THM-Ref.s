%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IqYTjU0bA3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:00 EST 2020

% Result     : Theorem 3.54s
% Output     : Refutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 153 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   24
%              Number of atoms          :  916 (1565 expanded)
%              Number of equality atoms :   65 ( 108 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( X8 = X7 )
      | ( X8 = X4 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X8 = X4 )
      | ( X8 = X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X2 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X2 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X2 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('52',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X13 )
      | ( X13
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k11_relat_1 @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( sk_C_1 @ X14 @ X13 )
       != X14 )
      | ( X13
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k9_relat_1 @ X17 @ X18 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IqYTjU0bA3
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.54/3.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.54/3.78  % Solved by: fo/fo7.sh
% 3.54/3.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.54/3.78  % done 4695 iterations in 3.322s
% 3.54/3.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.54/3.78  % SZS output start Refutation
% 3.54/3.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.54/3.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.54/3.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.54/3.78  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.54/3.78  thf(sk_B_type, type, sk_B: $i).
% 3.54/3.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.54/3.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.54/3.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.54/3.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.54/3.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.54/3.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.54/3.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.54/3.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.54/3.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.54/3.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.54/3.78  thf(sk_A_type, type, sk_A: $i).
% 3.54/3.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.54/3.78  thf(t3_xboole_0, axiom,
% 3.54/3.78    (![A:$i,B:$i]:
% 3.54/3.78     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.54/3.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.54/3.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.54/3.78            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.54/3.78  thf('0', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf(t204_relat_1, axiom,
% 3.54/3.78    (![A:$i,B:$i,C:$i]:
% 3.54/3.78     ( ( v1_relat_1 @ C ) =>
% 3.54/3.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 3.54/3.78         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 3.54/3.78  thf('1', plain,
% 3.54/3.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 3.54/3.78          | ~ (v1_relat_1 @ X20))),
% 3.54/3.78      inference('cnf', [status(esa)], [t204_relat_1])).
% 3.54/3.78  thf('2', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r2_hidden @ 
% 3.54/3.78             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 3.54/3.78      inference('sup-', [status(thm)], ['0', '1'])).
% 3.54/3.78  thf(t8_funct_1, axiom,
% 3.54/3.78    (![A:$i,B:$i,C:$i]:
% 3.54/3.78     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.54/3.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 3.54/3.78         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 3.54/3.78           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 3.54/3.78  thf('3', plain,
% 3.54/3.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.54/3.78         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.54/3.78          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 3.54/3.78          | ~ (v1_funct_1 @ X23)
% 3.54/3.78          | ~ (v1_relat_1 @ X23))),
% 3.54/3.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.54/3.78  thf('4', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         (~ (v1_relat_1 @ X0)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X0)
% 3.54/3.78          | ~ (v1_funct_1 @ X0)
% 3.54/3.78          | ((sk_C @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['2', '3'])).
% 3.54/3.78  thf('5', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         (((sk_C @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1))
% 3.54/3.78          | ~ (v1_funct_1 @ X0)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X0))),
% 3.54/3.78      inference('simplify', [status(thm)], ['4'])).
% 3.54/3.78  thf('6', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf('7', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         ((r2_hidden @ (k1_funct_1 @ X1 @ X0) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 3.54/3.78          | ~ (v1_funct_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2))),
% 3.54/3.78      inference('sup+', [status(thm)], ['5', '6'])).
% 3.54/3.78  thf('8', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         (~ (v1_funct_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ X2))),
% 3.54/3.78      inference('simplify', [status(thm)], ['7'])).
% 3.54/3.78  thf(t70_enumset1, axiom,
% 3.54/3.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.54/3.78  thf('9', plain,
% 3.54/3.78      (![X11 : $i, X12 : $i]:
% 3.54/3.78         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 3.54/3.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.54/3.78  thf(t69_enumset1, axiom,
% 3.54/3.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.54/3.78  thf('10', plain,
% 3.54/3.78      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 3.54/3.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.54/3.78  thf('11', plain,
% 3.54/3.78      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.54/3.78      inference('sup+', [status(thm)], ['9', '10'])).
% 3.54/3.78  thf('12', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf('13', plain,
% 3.54/3.78      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.54/3.78      inference('sup+', [status(thm)], ['9', '10'])).
% 3.54/3.78  thf('14', plain,
% 3.54/3.78      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 3.54/3.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.54/3.78  thf(d2_tarski, axiom,
% 3.54/3.78    (![A:$i,B:$i,C:$i]:
% 3.54/3.78     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 3.54/3.78       ( ![D:$i]:
% 3.54/3.78         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 3.54/3.78  thf('15', plain,
% 3.54/3.78      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X8 @ X6)
% 3.54/3.78          | ((X8) = (X7))
% 3.54/3.78          | ((X8) = (X4))
% 3.54/3.78          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 3.54/3.78      inference('cnf', [status(esa)], [d2_tarski])).
% 3.54/3.78  thf('16', plain,
% 3.54/3.78      (![X4 : $i, X7 : $i, X8 : $i]:
% 3.54/3.78         (((X8) = (X4))
% 3.54/3.78          | ((X8) = (X7))
% 3.54/3.78          | ~ (r2_hidden @ X8 @ (k2_tarski @ X7 @ X4)))),
% 3.54/3.78      inference('simplify', [status(thm)], ['15'])).
% 3.54/3.78  thf('17', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['14', '16'])).
% 3.54/3.78  thf('18', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 3.54/3.78      inference('simplify', [status(thm)], ['17'])).
% 3.54/3.78  thf('19', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0)) | ((X1) = (X0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['13', '18'])).
% 3.54/3.78  thf('20', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0))
% 3.54/3.78          | ((sk_C @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1) = (X0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['12', '19'])).
% 3.54/3.78  thf('21', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r2_hidden @ 
% 3.54/3.78             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 3.54/3.78      inference('sup-', [status(thm)], ['0', '1'])).
% 3.54/3.78  thf('22', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         ((r2_hidden @ (k4_tarski @ X2 @ X0) @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X2) @ 
% 3.54/3.78             (k1_enumset1 @ X0 @ X0 @ X0))
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X2) @ 
% 3.54/3.78             (k1_enumset1 @ X0 @ X0 @ X0)))),
% 3.54/3.78      inference('sup+', [status(thm)], ['20', '21'])).
% 3.54/3.78  thf('23', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         (~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X2) @ 
% 3.54/3.78             (k1_enumset1 @ X0 @ X0 @ X0))
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ X1))),
% 3.54/3.78      inference('simplify', [status(thm)], ['22'])).
% 3.54/3.78  thf(t117_funct_1, conjecture,
% 3.54/3.78    (![A:$i,B:$i]:
% 3.54/3.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.54/3.78       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.54/3.78         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 3.54/3.78  thf(zf_stmt_0, negated_conjecture,
% 3.54/3.78    (~( ![A:$i,B:$i]:
% 3.54/3.78        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.54/3.78          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.54/3.78            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 3.54/3.78    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 3.54/3.78  thf('24', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('25', plain,
% 3.54/3.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 3.54/3.78          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.54/3.78          | ~ (v1_funct_1 @ X23)
% 3.54/3.78          | ~ (v1_relat_1 @ X23))),
% 3.54/3.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.54/3.78  thf('26', plain,
% 3.54/3.78      (![X22 : $i, X23 : $i]:
% 3.54/3.78         (~ (v1_relat_1 @ X23)
% 3.54/3.78          | ~ (v1_funct_1 @ X23)
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 3.54/3.78          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 3.54/3.78      inference('simplify', [status(thm)], ['25'])).
% 3.54/3.78  thf('27', plain,
% 3.54/3.78      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 3.54/3.78        | ~ (v1_funct_1 @ sk_B)
% 3.54/3.78        | ~ (v1_relat_1 @ sk_B))),
% 3.54/3.78      inference('sup-', [status(thm)], ['24', '26'])).
% 3.54/3.78  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('30', plain,
% 3.54/3.78      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 3.54/3.78      inference('demod', [status(thm)], ['27', '28', '29'])).
% 3.54/3.78  thf('31', plain,
% 3.54/3.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.54/3.78         (~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 3.54/3.78          | (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 3.54/3.78          | ~ (v1_relat_1 @ X20))),
% 3.54/3.78      inference('cnf', [status(esa)], [t204_relat_1])).
% 3.54/3.78  thf('32', plain,
% 3.54/3.78      ((~ (v1_relat_1 @ sk_B)
% 3.54/3.78        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['30', '31'])).
% 3.54/3.78  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('34', plain,
% 3.54/3.78      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 3.54/3.78      inference('demod', [status(thm)], ['32', '33'])).
% 3.54/3.78  thf('35', plain,
% 3.54/3.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X2 @ X0)
% 3.54/3.78          | ~ (r2_hidden @ X2 @ X3)
% 3.54/3.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf('36', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (~ (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ X0)
% 3.54/3.78          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0))),
% 3.54/3.78      inference('sup-', [status(thm)], ['34', '35'])).
% 3.54/3.78  thf('37', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 3.54/3.78          | ~ (v1_relat_1 @ sk_B)
% 3.54/3.78          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 3.54/3.78               (k1_enumset1 @ X0 @ X0 @ X0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['23', '36'])).
% 3.54/3.78  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('39', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 3.54/3.78          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 3.54/3.78               (k1_enumset1 @ X0 @ X0 @ X0)))),
% 3.54/3.78      inference('demod', [status(thm)], ['37', '38'])).
% 3.54/3.78  thf('40', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 3.54/3.78      inference('sup-', [status(thm)], ['11', '39'])).
% 3.54/3.78  thf('41', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (~ (v1_relat_1 @ sk_B)
% 3.54/3.78          | (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 3.54/3.78          | ~ (v1_funct_1 @ sk_B)
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 3.54/3.78      inference('sup-', [status(thm)], ['8', '40'])).
% 3.54/3.78  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('44', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 3.54/3.78          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 3.54/3.78      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.54/3.78  thf('45', plain,
% 3.54/3.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.54/3.78         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.54/3.78          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 3.54/3.78          | ~ (v1_funct_1 @ X23)
% 3.54/3.78          | ~ (v1_relat_1 @ X23))),
% 3.54/3.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.54/3.78  thf('46', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 3.54/3.78          | ~ (v1_relat_1 @ sk_B)
% 3.54/3.78          | ~ (v1_funct_1 @ sk_B)
% 3.54/3.78          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['44', '45'])).
% 3.54/3.78  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('49', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 3.54/3.78          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 3.54/3.78      inference('demod', [status(thm)], ['46', '47', '48'])).
% 3.54/3.78  thf('50', plain,
% 3.54/3.78      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 3.54/3.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.54/3.78  thf('51', plain,
% 3.54/3.78      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.54/3.78         (((X5) != (X4))
% 3.54/3.78          | (r2_hidden @ X5 @ X6)
% 3.54/3.78          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 3.54/3.78      inference('cnf', [status(esa)], [d2_tarski])).
% 3.54/3.78  thf('52', plain,
% 3.54/3.78      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 3.54/3.78      inference('simplify', [status(thm)], ['51'])).
% 3.54/3.78  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.54/3.78      inference('sup+', [status(thm)], ['50', '52'])).
% 3.54/3.78  thf(l44_zfmisc_1, axiom,
% 3.54/3.78    (![A:$i,B:$i]:
% 3.54/3.78     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.54/3.78          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 3.54/3.78  thf('54', plain,
% 3.54/3.78      (![X13 : $i, X14 : $i]:
% 3.54/3.78         (((X13) = (k1_xboole_0))
% 3.54/3.78          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X13)
% 3.54/3.78          | ((X13) = (k1_tarski @ X14)))),
% 3.54/3.78      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.54/3.78  thf('55', plain,
% 3.54/3.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X2 @ X0)
% 3.54/3.78          | ~ (r2_hidden @ X2 @ X3)
% 3.54/3.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf('56', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.78         (((X0) = (k1_tarski @ X1))
% 3.54/3.78          | ((X0) = (k1_xboole_0))
% 3.54/3.78          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.54/3.78          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 3.54/3.78      inference('sup-', [status(thm)], ['54', '55'])).
% 3.54/3.78  thf('57', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ (sk_C_1 @ X1 @ X0)))
% 3.54/3.78          | ((X0) = (k1_xboole_0))
% 3.54/3.78          | ((X0) = (k1_tarski @ X1)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['53', '56'])).
% 3.54/3.78  thf('58', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (((sk_C_1 @ X0 @ (k11_relat_1 @ sk_B @ sk_A))
% 3.54/3.78            = (k1_funct_1 @ sk_B @ sk_A))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['49', '57'])).
% 3.54/3.78  thf('59', plain,
% 3.54/3.78      (![X13 : $i, X14 : $i]:
% 3.54/3.78         (((X13) = (k1_xboole_0))
% 3.54/3.78          | ((sk_C_1 @ X14 @ X13) != (X14))
% 3.54/3.78          | ((X13) = (k1_tarski @ X14)))),
% 3.54/3.78      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.54/3.78  thf('60', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 3.54/3.78          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['58', '59'])).
% 3.54/3.78  thf('61', plain,
% 3.54/3.78      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 3.54/3.78        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.54/3.78      inference('simplify', [status(thm)], ['60'])).
% 3.54/3.78  thf('62', plain,
% 3.54/3.78      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('63', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 3.54/3.78      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 3.54/3.78  thf(d16_relat_1, axiom,
% 3.54/3.78    (![A:$i]:
% 3.54/3.78     ( ( v1_relat_1 @ A ) =>
% 3.54/3.78       ( ![B:$i]:
% 3.54/3.78         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 3.54/3.78  thf('64', plain,
% 3.54/3.78      (![X15 : $i, X16 : $i]:
% 3.54/3.78         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 3.54/3.78          | ~ (v1_relat_1 @ X15))),
% 3.54/3.78      inference('cnf', [status(esa)], [d16_relat_1])).
% 3.54/3.78  thf(t151_relat_1, axiom,
% 3.54/3.78    (![A:$i,B:$i]:
% 3.54/3.78     ( ( v1_relat_1 @ B ) =>
% 3.54/3.78       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 3.54/3.78         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.54/3.78  thf('65', plain,
% 3.54/3.78      (![X17 : $i, X18 : $i]:
% 3.54/3.78         (((k9_relat_1 @ X17 @ X18) != (k1_xboole_0))
% 3.54/3.78          | (r1_xboole_0 @ (k1_relat_1 @ X17) @ X18)
% 3.54/3.78          | ~ (v1_relat_1 @ X17))),
% 3.54/3.78      inference('cnf', [status(esa)], [t151_relat_1])).
% 3.54/3.78  thf('66', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['64', '65'])).
% 3.54/3.78  thf('67', plain,
% 3.54/3.78      (![X0 : $i, X1 : $i]:
% 3.54/3.78         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 3.54/3.78          | ~ (v1_relat_1 @ X1)
% 3.54/3.78          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 3.54/3.78      inference('simplify', [status(thm)], ['66'])).
% 3.54/3.78  thf('68', plain,
% 3.54/3.78      ((((k1_xboole_0) != (k1_xboole_0))
% 3.54/3.78        | ~ (v1_relat_1 @ sk_B)
% 3.54/3.78        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 3.54/3.78      inference('sup-', [status(thm)], ['63', '67'])).
% 3.54/3.78  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('70', plain,
% 3.54/3.78      ((((k1_xboole_0) != (k1_xboole_0))
% 3.54/3.78        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 3.54/3.78      inference('demod', [status(thm)], ['68', '69'])).
% 3.54/3.78  thf('71', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))),
% 3.54/3.78      inference('simplify', [status(thm)], ['70'])).
% 3.54/3.78  thf('72', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.54/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.78  thf('73', plain,
% 3.54/3.78      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.54/3.78         (~ (r2_hidden @ X2 @ X0)
% 3.54/3.78          | ~ (r2_hidden @ X2 @ X3)
% 3.54/3.78          | ~ (r1_xboole_0 @ X0 @ X3))),
% 3.54/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.54/3.78  thf('74', plain,
% 3.54/3.78      (![X0 : $i]:
% 3.54/3.78         (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 3.54/3.78          | ~ (r2_hidden @ sk_A @ X0))),
% 3.54/3.78      inference('sup-', [status(thm)], ['72', '73'])).
% 3.54/3.78  thf('75', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 3.54/3.78      inference('sup-', [status(thm)], ['71', '74'])).
% 3.54/3.78  thf('76', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.54/3.78      inference('sup+', [status(thm)], ['50', '52'])).
% 3.54/3.78  thf('77', plain, ($false), inference('demod', [status(thm)], ['75', '76'])).
% 3.54/3.78  
% 3.54/3.78  % SZS output end Refutation
% 3.54/3.78  
% 3.54/3.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
