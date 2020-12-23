%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.enETkP3ggi

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:46 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 826 expanded)
%              Number of leaves         :   23 ( 239 expanded)
%              Depth                    :   21
%              Number of atoms          :  851 (9159 expanded)
%              Number of equality atoms :   69 ( 718 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ ( sk_E @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( ( ( k3_xboole_0 @ X21 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X21 ) @ ( k2_relat_1 @ X21 ) ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ ( sk_E @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('46',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['34','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['15'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','27'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['15'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ ( sk_F @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) @ ( sk_F @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['15'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X2 @ X2 )
        = ( k5_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X2 @ X2 )
        = ( k5_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('66',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('68',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('73',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','73'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.enETkP3ggi
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.38/1.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.63  % Solved by: fo/fo7.sh
% 1.38/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.63  % done 1171 iterations in 1.134s
% 1.38/1.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.63  % SZS output start Refutation
% 1.38/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.38/1.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.38/1.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.38/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.63  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 1.38/1.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.38/1.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.38/1.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.63  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.38/1.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.38/1.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.63  thf(d8_relat_1, axiom,
% 1.38/1.63    (![A:$i]:
% 1.38/1.63     ( ( v1_relat_1 @ A ) =>
% 1.38/1.63       ( ![B:$i]:
% 1.38/1.63         ( ( v1_relat_1 @ B ) =>
% 1.38/1.63           ( ![C:$i]:
% 1.38/1.63             ( ( v1_relat_1 @ C ) =>
% 1.38/1.63               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 1.38/1.63                 ( ![D:$i,E:$i]:
% 1.38/1.63                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 1.38/1.63                     ( ?[F:$i]:
% 1.38/1.63                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 1.38/1.63                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 1.38/1.63  thf('0', plain,
% 1.38/1.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X11)
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 1.38/1.63             X13)
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_F @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 1.38/1.63             X11)
% 1.38/1.63          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 1.38/1.63          | ~ (v1_relat_1 @ X13)
% 1.38/1.63          | ~ (v1_relat_1 @ X12))),
% 1.38/1.63      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.38/1.63  thf(d5_xboole_0, axiom,
% 1.38/1.63    (![A:$i,B:$i,C:$i]:
% 1.38/1.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.38/1.63       ( ![D:$i]:
% 1.38/1.63         ( ( r2_hidden @ D @ C ) <=>
% 1.38/1.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.38/1.63  thf('1', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.38/1.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.38/1.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.38/1.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.63  thf('2', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.38/1.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.38/1.63          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.38/1.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.38/1.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.63  thf('3', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.38/1.63          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.38/1.63          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.38/1.63      inference('sup-', [status(thm)], ['1', '2'])).
% 1.38/1.63  thf('4', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.38/1.63      inference('simplify', [status(thm)], ['3'])).
% 1.38/1.63  thf('5', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.38/1.63         (~ (r2_hidden @ X4 @ X3)
% 1.38/1.63          | (r2_hidden @ X4 @ X1)
% 1.38/1.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.63  thf('6', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.38/1.63         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.63      inference('simplify', [status(thm)], ['5'])).
% 1.38/1.63  thf('7', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 1.38/1.63          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['4', '6'])).
% 1.38/1.63  thf('8', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.38/1.63      inference('simplify', [status(thm)], ['3'])).
% 1.38/1.63  thf('9', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.38/1.63         (~ (r2_hidden @ X4 @ X3)
% 1.38/1.63          | ~ (r2_hidden @ X4 @ X2)
% 1.38/1.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.63  thf('10', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.38/1.63         (~ (r2_hidden @ X4 @ X2)
% 1.38/1.63          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.63      inference('simplify', [status(thm)], ['9'])).
% 1.38/1.63  thf('11', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 1.38/1.63          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 1.38/1.63      inference('sup-', [status(thm)], ['8', '10'])).
% 1.38/1.63  thf('12', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.38/1.63          | ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.38/1.63      inference('sup-', [status(thm)], ['7', '11'])).
% 1.38/1.63  thf('13', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('simplify', [status(thm)], ['12'])).
% 1.38/1.63  thf('14', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.38/1.63         (~ (r2_hidden @ X4 @ X2)
% 1.38/1.63          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.63      inference('simplify', [status(thm)], ['9'])).
% 1.38/1.63  thf('15', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ~ (r2_hidden @ X2 @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['13', '14'])).
% 1.38/1.63  thf('16', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('condensation', [status(thm)], ['15'])).
% 1.38/1.63  thf('17', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ((k4_xboole_0 @ X0 @ X0) = (k5_relat_1 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_F @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1) @ 
% 1.38/1.63              (sk_E @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1)) @ 
% 1.38/1.63             X2)
% 1.38/1.63          | ~ (v1_relat_1 @ X2))),
% 1.38/1.63      inference('sup-', [status(thm)], ['0', '16'])).
% 1.38/1.63  thf(t92_xboole_1, axiom,
% 1.38/1.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.38/1.63  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 1.38/1.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.38/1.63  thf(t62_relat_1, conjecture,
% 1.38/1.63    (![A:$i]:
% 1.38/1.63     ( ( v1_relat_1 @ A ) =>
% 1.38/1.63       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.38/1.63         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.38/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.63    (~( ![A:$i]:
% 1.38/1.63        ( ( v1_relat_1 @ A ) =>
% 1.38/1.63          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.38/1.63            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.38/1.63    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.38/1.63  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 1.38/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.63  thf('20', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 1.38/1.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.38/1.63  thf(t22_relat_1, axiom,
% 1.38/1.63    (![A:$i]:
% 1.38/1.63     ( ( v1_relat_1 @ A ) =>
% 1.38/1.63       ( ( k3_xboole_0 @
% 1.38/1.63           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 1.38/1.63         ( A ) ) ))).
% 1.38/1.63  thf('21', plain,
% 1.38/1.63      (![X21 : $i]:
% 1.38/1.63         (((k3_xboole_0 @ X21 @ 
% 1.38/1.63            (k2_zfmisc_1 @ (k1_relat_1 @ X21) @ (k2_relat_1 @ X21))) = (
% 1.38/1.63            X21))
% 1.38/1.63          | ~ (v1_relat_1 @ X21))),
% 1.38/1.63      inference('cnf', [status(esa)], [t22_relat_1])).
% 1.38/1.63  thf(t100_xboole_1, axiom,
% 1.38/1.63    (![A:$i,B:$i]:
% 1.38/1.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.38/1.63  thf('22', plain,
% 1.38/1.63      (![X6 : $i, X7 : $i]:
% 1.38/1.63         ((k4_xboole_0 @ X6 @ X7)
% 1.38/1.63           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.38/1.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.38/1.63  thf('23', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X0 @ 
% 1.38/1.63            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.38/1.63            = (k5_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('sup+', [status(thm)], ['21', '22'])).
% 1.38/1.63  thf(fc2_relat_1, axiom,
% 1.38/1.63    (![A:$i,B:$i]:
% 1.38/1.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 1.38/1.63  thf('24', plain,
% 1.38/1.63      (![X19 : $i, X20 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k4_xboole_0 @ X19 @ X20)))),
% 1.38/1.63      inference('cnf', [status(esa)], [fc2_relat_1])).
% 1.38/1.63  thf('25', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         ((v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ~ (v1_relat_1 @ X0)
% 1.38/1.63          | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('sup+', [status(thm)], ['23', '24'])).
% 1.38/1.63  thf('26', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.38/1.63      inference('simplify', [status(thm)], ['25'])).
% 1.38/1.63  thf('27', plain,
% 1.38/1.63      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('sup+', [status(thm)], ['20', '26'])).
% 1.38/1.63  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.38/1.63      inference('sup-', [status(thm)], ['19', '27'])).
% 1.38/1.63  thf('29', plain, (![X0 : $i]: (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('sup+', [status(thm)], ['18', '28'])).
% 1.38/1.63  thf('30', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('simplify', [status(thm)], ['12'])).
% 1.38/1.63  thf('31', plain,
% 1.38/1.63      (![X19 : $i, X20 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k4_xboole_0 @ X19 @ X20)))),
% 1.38/1.63      inference('cnf', [status(esa)], [fc2_relat_1])).
% 1.38/1.63  thf('32', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         ((v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)) | ~ (v1_relat_1 @ X1))),
% 1.38/1.63      inference('sup+', [status(thm)], ['30', '31'])).
% 1.38/1.63  thf('33', plain, (![X1 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['29', '32'])).
% 1.38/1.63  thf('34', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k4_xboole_0 @ X0 @ X0) = (k5_relat_1 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_F @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1) @ 
% 1.38/1.63              (sk_E @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1)) @ 
% 1.38/1.63             X2)
% 1.38/1.63          | ~ (v1_relat_1 @ X2))),
% 1.38/1.63      inference('demod', [status(thm)], ['17', '33'])).
% 1.38/1.63  thf('35', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X0 @ 
% 1.38/1.63            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.38/1.63            = (k5_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('sup+', [status(thm)], ['21', '22'])).
% 1.38/1.63  thf('36', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.38/1.63         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.38/1.63          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.38/1.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.63  thf('37', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.38/1.63          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.38/1.63      inference('eq_fact', [status(thm)], ['36'])).
% 1.38/1.63  thf('38', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('condensation', [status(thm)], ['15'])).
% 1.38/1.63  thf('39', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]:
% 1.38/1.63         ((k4_xboole_0 @ X0 @ X0)
% 1.38/1.63           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['37', '38'])).
% 1.38/1.63  thf('40', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (((k4_xboole_0 @ X0 @ X0)
% 1.38/1.63            = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))
% 1.38/1.63          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.38/1.63      inference('sup+', [status(thm)], ['35', '39'])).
% 1.38/1.63  thf('41', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 1.38/1.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.38/1.63  thf('42', plain, (![X1 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['29', '32'])).
% 1.38/1.63  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('46', plain,
% 1.38/1.63      (![X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 1.38/1.63              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 1.38/1.63             X2)
% 1.38/1.63          | ~ (v1_relat_1 @ X2))),
% 1.38/1.63      inference('demod', [status(thm)], ['34', '43', '44', '45'])).
% 1.38/1.63  thf('47', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('condensation', [status(thm)], ['15'])).
% 1.38/1.63  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.38/1.63      inference('demod', [status(thm)], ['47', '48'])).
% 1.38/1.63  thf('50', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ k1_xboole_0)
% 1.38/1.63          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.38/1.63          | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('sup-', [status(thm)], ['46', '49'])).
% 1.38/1.63  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.38/1.63      inference('sup-', [status(thm)], ['19', '27'])).
% 1.38/1.63  thf('52', plain,
% 1.38/1.63      (![X0 : $i]:
% 1.38/1.63         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.38/1.63          | ~ (v1_relat_1 @ X0))),
% 1.38/1.63      inference('demod', [status(thm)], ['50', '51'])).
% 1.38/1.63  thf('53', plain,
% 1.38/1.63      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.38/1.63        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.38/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.63  thf('54', plain,
% 1.38/1.63      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.38/1.63         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.38/1.63      inference('split', [status(esa)], ['53'])).
% 1.38/1.63  thf('55', plain,
% 1.38/1.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X11)
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 1.38/1.63             X13)
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_F @ X13 @ X11 @ X12)) @ 
% 1.38/1.63             X12)
% 1.38/1.63          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 1.38/1.63          | ~ (v1_relat_1 @ X13)
% 1.38/1.63          | ~ (v1_relat_1 @ X12))),
% 1.38/1.63      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.38/1.63  thf('56', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('condensation', [status(thm)], ['15'])).
% 1.38/1.63  thf('57', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))
% 1.38/1.63          | ((k4_xboole_0 @ X0 @ X0) = (k5_relat_1 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_D_1 @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1) @ 
% 1.38/1.63              (sk_F @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1)) @ 
% 1.38/1.63             X1)
% 1.38/1.63          | ~ (v1_relat_1 @ X2))),
% 1.38/1.63      inference('sup-', [status(thm)], ['55', '56'])).
% 1.38/1.63  thf('58', plain, (![X1 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['29', '32'])).
% 1.38/1.63  thf('59', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k4_xboole_0 @ X0 @ X0) = (k5_relat_1 @ X1 @ X2))
% 1.38/1.63          | (r2_hidden @ 
% 1.38/1.63             (k4_tarski @ (sk_D_1 @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1) @ 
% 1.38/1.63              (sk_F @ (k4_xboole_0 @ X0 @ X0) @ X2 @ X1)) @ 
% 1.38/1.63             X1)
% 1.38/1.63          | ~ (v1_relat_1 @ X2))),
% 1.38/1.63      inference('demod', [status(thm)], ['57', '58'])).
% 1.38/1.63  thf('60', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.63      inference('condensation', [status(thm)], ['15'])).
% 1.38/1.63  thf('61', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k4_xboole_0 @ X2 @ X2)
% 1.38/1.63              = (k5_relat_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 1.38/1.63          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.38/1.63      inference('sup-', [status(thm)], ['59', '60'])).
% 1.38/1.63  thf('62', plain, (![X1 : $i]: (v1_relat_1 @ (k4_xboole_0 @ X1 @ X1))),
% 1.38/1.63      inference('sup-', [status(thm)], ['29', '32'])).
% 1.38/1.63  thf('63', plain,
% 1.38/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k4_xboole_0 @ X2 @ X2)
% 1.38/1.63              = (k5_relat_1 @ (k4_xboole_0 @ X0 @ X0) @ X1)))),
% 1.38/1.63      inference('demod', [status(thm)], ['61', '62'])).
% 1.38/1.63  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.38/1.63  thf('66', plain,
% 1.38/1.63      (![X1 : $i]:
% 1.38/1.63         (~ (v1_relat_1 @ X1)
% 1.38/1.63          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 1.38/1.63      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.38/1.63  thf('67', plain,
% 1.38/1.63      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.38/1.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.38/1.63      inference('split', [status(esa)], ['53'])).
% 1.38/1.63  thf('68', plain,
% 1.38/1.63      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 1.38/1.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.38/1.63      inference('sup-', [status(thm)], ['66', '67'])).
% 1.38/1.63  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 1.38/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.63  thf('70', plain,
% 1.38/1.63      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.38/1.63         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.38/1.63      inference('demod', [status(thm)], ['68', '69'])).
% 1.38/1.63  thf('71', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.38/1.63      inference('simplify', [status(thm)], ['70'])).
% 1.38/1.63  thf('72', plain,
% 1.38/1.63      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.38/1.63       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.38/1.63      inference('split', [status(esa)], ['53'])).
% 1.38/1.63  thf('73', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.38/1.63      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 1.38/1.63  thf('74', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 1.38/1.63      inference('simpl_trail', [status(thm)], ['54', '73'])).
% 1.38/1.63  thf('75', plain,
% 1.38/1.63      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 1.38/1.63      inference('sup-', [status(thm)], ['52', '74'])).
% 1.38/1.63  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 1.38/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.63  thf('77', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.38/1.63      inference('demod', [status(thm)], ['75', '76'])).
% 1.38/1.63  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 1.38/1.63  
% 1.38/1.63  % SZS output end Refutation
% 1.38/1.63  
% 1.38/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
