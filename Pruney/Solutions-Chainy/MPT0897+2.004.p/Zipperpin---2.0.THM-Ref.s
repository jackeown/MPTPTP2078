%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rr6LoPDE74

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:40 EST 2020

% Result     : Theorem 11.05s
% Output     : Refutation 11.05s
% Verified   : 
% Statistics : Number of formulae       :  434 (65691 expanded)
%              Number of leaves         :   29 (20175 expanded)
%              Depth                    :  100
%              Number of atoms          : 4899 (715711 expanded)
%              Number of equality atoms :  960 (107479 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t57_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
            = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_mcart_1])).

thf('24',plain,(
    ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = sk_D )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
        = sk_D ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D )
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('55',plain,
    ( ( sk_D = sk_H )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D )
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference('sup+',[status(thm)],['44','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_D = sk_H )
      | ( sk_D = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_H )
     != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D = sk_H )
      | ( sk_D = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_D = sk_H )
      | ( sk_D = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('72',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference('simplify_reflect+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_D = sk_H )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','84'])).

thf('86',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_D = sk_H ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_D = sk_H ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('92',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_D = sk_H ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['40','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('100',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['40','95'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('106',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
       != ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['40','95'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('117',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('118',plain,
    ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','116','117'])).

thf('119',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','118'])).

thf('120',plain,
    ( ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('124',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['40','95'])).

thf('125',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('126',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X0 ) @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ) @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('131',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ) @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['122','135'])).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('138',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','138'])).

thf('140',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
        = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
      | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
        = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
      | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
        = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('151',plain,
    ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('152',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
       != ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
        = k1_xboole_0 )
      | ( sk_B_1 = X1 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B_1 = X1 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
        = k1_xboole_0 )
      | ( sk_B_1 = X1 ) ) ),
    inference('sup-',[status(thm)],['150','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B_1 = X1 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B_1 = X1 )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_F ) ),
    inference(eq_res,[status(thm)],['158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('161',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('163',plain,
    ( ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_B_1 = sk_F )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( sk_H = k1_xboole_0 )
      | ( sk_B_1 = sk_F )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('169',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_B_1 = sk_F ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_B_1 = sk_F ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('174',plain,(
    sk_B_1 = sk_F ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    sk_B_1 = sk_F ),
    inference(clc,[status(thm)],['172','173'])).

thf('176',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_F ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_F )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','174','175'])).

thf('177',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('178',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_A_1 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( sk_E = sk_A_1 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_F )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','178'])).

thf('180',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = sk_A_1 ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( sk_A_1 != sk_E )
    | ( sk_B_1 != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( sk_A_1 != sk_E )
   <= ( sk_A_1 != sk_E ) ),
    inference(split,[status(esa)],['181'])).

thf('183',plain,(
    sk_D = sk_H ),
    inference('sup-',[status(thm)],['90','94'])).

thf('184',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['181'])).

thf('185',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('188',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['181'])).

thf('189',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = X0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) )
        = ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['40','95'])).

thf('200',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['115'])).

thf('201',plain,
    ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = X0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) )
        = ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('203',plain,
    ( ( ( k1_relat_1 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['198','203'])).

thf('205',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('207',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['191','208'])).

thf('210',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('212',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ) @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('214',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('215',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ) ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('219',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['212','219'])).

thf('221',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('222',plain,
    ( ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('224',plain,
    ( ( sk_B_1 = sk_F )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_G )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_B_1 = sk_F )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['224','231'])).

thf('233',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_G )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_B_1 = sk_F )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('236',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = sk_F ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('239',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('240',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('242',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('244',plain,
    ( ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('246',plain,
    ( ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('248',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_F ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_B_1 = sk_F ) ),
    inference('sup+',[status(thm)],['237','249'])).

thf('251',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('253',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('255',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('259',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('262',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['253','262'])).

thf('264',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('265',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('267',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('268',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['265','268'])).

thf('270',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('271',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['269','270'])).

thf('272',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('273',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('275',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('277',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('278',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['276','277'])).

thf('279',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('280',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('282',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('284',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['275','285'])).

thf('287',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('288',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('290',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('291',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('295',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference(simplify,[status(thm)],['295'])).

thf('297',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('298',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('299',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_G = sk_F )
    | ( sk_B_1 = sk_F ) ),
    inference('sup+',[status(thm)],['297','298'])).

thf('300',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('301',plain,
    ( ( sk_B_1 = sk_F )
    | ( sk_G = sk_F ) ),
    inference(clc,[status(thm)],['299','300'])).

thf('302',plain,
    ( ( sk_B_1 != sk_F )
   <= ( sk_B_1 != sk_F ) ),
    inference(split,[status(esa)],['181'])).

thf('303',plain,
    ( ( ( sk_F != sk_F )
      | ( sk_G = sk_F ) )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,
    ( ( sk_G = sk_F )
   <= ( sk_B_1 != sk_F ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ( sk_B_1 = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('306',plain,
    ( ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_F )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_B_1 = sk_F ) )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup+',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( sk_B_1 != sk_F )
   <= ( sk_B_1 != sk_F ) ),
    inference(split,[status(esa)],['181'])).

thf('308',plain,
    ( ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_F )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ( sk_B_1 != sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('310',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_H = k1_xboole_0 )
        | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('312',plain,
    ( ! [X0: $i] :
        ( ( sk_H = k1_xboole_0 )
        | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 != sk_F ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( sk_G = sk_F )
   <= ( sk_B_1 != sk_F ) ),
    inference(simplify,[status(thm)],['303'])).

thf('314',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('315',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ sk_H )
     != k1_xboole_0 )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup-',[status(thm)],['312','315'])).

thf('317',plain,
    ( ( sk_H = k1_xboole_0 )
   <= ( sk_B_1 != sk_F ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('319',plain,
    ( ( v1_xboole_0 @ sk_H )
   <= ( sk_B_1 != sk_F ) ),
    inference('sup+',[status(thm)],['317','318'])).

thf('320',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('321',plain,(
    sk_B_1 = sk_F ),
    inference('sup-',[status(thm)],['319','320'])).

thf('322',plain,
    ( ( sk_A_1 != sk_E )
    | ( sk_B_1 != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['181'])).

thf('323',plain,(
    sk_A_1 != sk_E ),
    inference('sat_resolution*',[status(thm)],['186','190','321','322'])).

thf('324',plain,(
    sk_A_1 != sk_E ),
    inference(simpl_trail,[status(thm)],['182','323'])).

thf('325',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['180','324'])).

thf('326',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('327',plain,(
    sk_B_1 = sk_F ),
    inference(clc,[status(thm)],['172','173'])).

thf('328',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['325','328'])).

thf('330',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('331',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('332',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('333',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('334',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_A_1 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['332','333'])).

thf('335',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('336',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_A_1 ) ),
    inference('sup-',[status(thm)],['334','335'])).

thf('337',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('338',plain,
    ( ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      = sk_A_1 ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X4 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('340',plain,
    ( ( sk_A_1 = sk_E )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['338','339'])).

thf('341',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('342',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_G )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A_1 = sk_E )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('344',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_G )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_A_1 = sk_E )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['342','343'])).

thf('345',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('346',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A_1 = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A_1 = sk_E ) ),
    inference(simplify,[status(thm)],['346'])).

thf('348',plain,(
    sk_B_1 = sk_F ),
    inference(clc,[status(thm)],['172','173'])).

thf('349',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A_1 = sk_E ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( sk_A_1 = sk_E )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,(
    sk_A_1 != sk_E ),
    inference(simpl_trail,[status(thm)],['182','323'])).

thf('352',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_G )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['350','351'])).

thf('353',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('354',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
        = X5 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('355',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_F )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['353','354'])).

thf('356',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_F ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ( sk_G = sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['352','356'])).

thf('358',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_F ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('360',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( sk_G = sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['358','359'])).

thf('361',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('362',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('364',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_G = sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['362','363'])).

thf('365',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('366',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('368',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( sk_G = sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['366','367'])).

thf('369',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference(simplify,[status(thm)],['284'])).

thf('370',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_F ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('372',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( sk_G = sk_F )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['370','371'])).

thf('373',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference(simplify,[status(thm)],['295'])).

thf('374',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_G = sk_F ) ),
    inference(clc,[status(thm)],['372','373'])).

thf('375',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('376',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_G = sk_F ) ),
    inference('sup+',[status(thm)],['374','375'])).

thf('377',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('378',plain,(
    sk_G = sk_F ),
    inference(clc,[status(thm)],['376','377'])).

thf('379',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['331','378'])).

thf('380',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['379'])).

thf('381',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('382',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('384',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['382','383'])).

thf('385',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('386',plain,(
    sk_G = sk_F ),
    inference(clc,[status(thm)],['376','377'])).

thf('387',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['385','386'])).

thf('388',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['384','387'])).

thf('389',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('391',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['389','390'])).

thf('392',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('393',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('395',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['393','394'])).

thf('396',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(simplify,[status(thm)],['93'])).

thf('397',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['395','396'])).

thf('398',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('399',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['397','398'])).

thf('400',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference(simplify,[status(thm)],['295'])).

thf('401',plain,(
    sk_E = k1_xboole_0 ),
    inference(clc,[status(thm)],['399','400'])).

thf('402',plain,(
    v1_xboole_0 @ sk_E ),
    inference(demod,[status(thm)],['32','401'])).

thf('403',plain,(
    $false ),
    inference(demod,[status(thm)],['31','402'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rr6LoPDE74
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 11.05/11.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.05/11.29  % Solved by: fo/fo7.sh
% 11.05/11.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.05/11.29  % done 13418 iterations in 10.823s
% 11.05/11.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.05/11.29  % SZS output start Refutation
% 11.05/11.29  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 11.05/11.29  thf(sk_G_type, type, sk_G: $i).
% 11.05/11.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.05/11.29  thf(sk_C_type, type, sk_C: $i).
% 11.05/11.29  thf(sk_A_type, type, sk_A: $i).
% 11.05/11.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.05/11.29  thf(sk_E_type, type, sk_E: $i).
% 11.05/11.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.05/11.29  thf(sk_F_type, type, sk_F: $i).
% 11.05/11.29  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 11.05/11.29  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 11.05/11.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.05/11.29  thf(sk_D_type, type, sk_D: $i).
% 11.05/11.29  thf(sk_A_1_type, type, sk_A_1: $i).
% 11.05/11.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.05/11.29  thf(sk_B_type, type, sk_B: $i > $i).
% 11.05/11.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.05/11.29  thf(sk_H_type, type, sk_H: $i).
% 11.05/11.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.05/11.29  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 11.05/11.29  thf(d1_xboole_0, axiom,
% 11.05/11.29    (![A:$i]:
% 11.05/11.29     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 11.05/11.29  thf('0', plain,
% 11.05/11.29      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf(t10_mcart_1, axiom,
% 11.05/11.29    (![A:$i,B:$i,C:$i]:
% 11.05/11.29     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 11.05/11.29       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 11.05/11.29         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 11.05/11.29  thf('1', plain,
% 11.05/11.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.05/11.29         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 11.05/11.29          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.05/11.29  thf('2', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 11.05/11.29          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 11.05/11.29      inference('sup-', [status(thm)], ['0', '1'])).
% 11.05/11.29  thf('3', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf('4', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['2', '3'])).
% 11.05/11.29  thf(l13_xboole_0, axiom,
% 11.05/11.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 11.05/11.29  thf('5', plain,
% 11.05/11.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.29  thf('6', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['4', '5'])).
% 11.05/11.29  thf(d3_zfmisc_1, axiom,
% 11.05/11.29    (![A:$i,B:$i,C:$i]:
% 11.05/11.29     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 11.05/11.29       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 11.05/11.29  thf('7', plain,
% 11.05/11.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.29           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.29      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.29  thf('8', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X2))),
% 11.05/11.29      inference('sup+', [status(thm)], ['6', '7'])).
% 11.05/11.29  thf('9', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['2', '3'])).
% 11.05/11.29  thf('10', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X2)
% 11.05/11.29          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 11.05/11.29      inference('sup+', [status(thm)], ['8', '9'])).
% 11.05/11.29  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 11.05/11.29  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 11.05/11.29      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 11.05/11.29  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 11.05/11.29      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 11.05/11.29  thf('13', plain,
% 11.05/11.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.29  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['12', '13'])).
% 11.05/11.29  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('16', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X2))),
% 11.05/11.29      inference('demod', [status(thm)], ['10', '15'])).
% 11.05/11.29  thf(d4_zfmisc_1, axiom,
% 11.05/11.29    (![A:$i,B:$i,C:$i,D:$i]:
% 11.05/11.29     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 11.05/11.29       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 11.05/11.29  thf('17', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('18', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['2', '3'])).
% 11.05/11.29  thf('19', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.29          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['17', '18'])).
% 11.05/11.29  thf('20', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (~ (v1_xboole_0 @ X2)
% 11.05/11.29          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['16', '19'])).
% 11.05/11.29  thf('21', plain,
% 11.05/11.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.29  thf('22', plain,
% 11.05/11.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.29  thf('23', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.29      inference('sup+', [status(thm)], ['21', '22'])).
% 11.05/11.29  thf(t57_mcart_1, conjecture,
% 11.05/11.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 11.05/11.29     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 11.05/11.29       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 11.05/11.29         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 11.05/11.29           ( ( D ) = ( H ) ) ) ) ))).
% 11.05/11.29  thf(zf_stmt_0, negated_conjecture,
% 11.05/11.29    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 11.05/11.29        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 11.05/11.29          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 11.05/11.29            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 11.05/11.29              ( ( D ) = ( H ) ) ) ) ) )),
% 11.05/11.29    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 11.05/11.29  thf('24', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D) != (k1_xboole_0))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('25', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (((X0) != (k1_xboole_0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X0)
% 11.05/11.29          | ~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['23', '24'])).
% 11.05/11.29  thf('26', plain,
% 11.05/11.29      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D))
% 11.05/11.29        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 11.05/11.29      inference('simplify', [status(thm)], ['25'])).
% 11.05/11.29  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('28', plain,
% 11.05/11.29      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D))),
% 11.05/11.29      inference('simplify_reflect+', [status(thm)], ['26', '27'])).
% 11.05/11.29  thf('29', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('30', plain,
% 11.05/11.29      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['28', '29'])).
% 11.05/11.29  thf('31', plain, (~ (v1_xboole_0 @ sk_E)),
% 11.05/11.29      inference('sup-', [status(thm)], ['20', '30'])).
% 11.05/11.29  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf(t195_relat_1, axiom,
% 11.05/11.29    (![A:$i,B:$i]:
% 11.05/11.29     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 11.05/11.29          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 11.05/11.29               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 11.05/11.29  thf('33', plain,
% 11.05/11.29      (![X4 : $i, X5 : $i]:
% 11.05/11.29         (((X4) = (k1_xboole_0))
% 11.05/11.29          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.29          | ((X5) = (k1_xboole_0)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.29  thf('34', plain,
% 11.05/11.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.29           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.29      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.29  thf('35', plain,
% 11.05/11.29      (![X4 : $i, X5 : $i]:
% 11.05/11.29         (((X4) = (k1_xboole_0))
% 11.05/11.29          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.29          | ((X5) = (k1_xboole_0)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.29  thf('36', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29            = (k2_zfmisc_1 @ X2 @ X1))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['34', '35'])).
% 11.05/11.29  thf('37', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('38', plain,
% 11.05/11.29      (![X4 : $i, X5 : $i]:
% 11.05/11.29         (((X4) = (k1_xboole_0))
% 11.05/11.29          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.29          | ((X5) = (k1_xboole_0)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.29  thf('39', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.29            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['37', '38'])).
% 11.05/11.29  thf('40', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('41', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['2', '3'])).
% 11.05/11.29  thf('42', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.29      inference('sup+', [status(thm)], ['21', '22'])).
% 11.05/11.29  thf('43', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (~ (v1_xboole_0 @ X1)
% 11.05/11.29          | ~ (v1_xboole_0 @ X2)
% 11.05/11.29          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['41', '42'])).
% 11.05/11.29  thf('44', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['4', '5'])).
% 11.05/11.29  thf('45', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('46', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('47', plain,
% 11.05/11.29      (![X4 : $i, X5 : $i]:
% 11.05/11.29         (((X4) = (k1_xboole_0))
% 11.05/11.29          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.29          | ((X5) = (k1_xboole_0)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.29  thf('48', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['46', '47'])).
% 11.05/11.29  thf('49', plain,
% 11.05/11.29      ((((k2_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)) = (sk_D))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['45', '48'])).
% 11.05/11.29  thf('50', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('51', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 11.05/11.29            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.29          | ((sk_D) = (k1_xboole_0))
% 11.05/11.29          | ((k2_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)) = (sk_D)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['49', '50'])).
% 11.05/11.29  thf('52', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('53', plain,
% 11.05/11.29      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_D)
% 11.05/11.29          = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29        | ((k2_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)) = (sk_D))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['51', '52'])).
% 11.05/11.29  thf('54', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['46', '47'])).
% 11.05/11.29  thf('55', plain,
% 11.05/11.29      ((((sk_D) = (sk_H))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((k2_zfmisc_1 @ k1_xboole_0 @ sk_D)
% 11.05/11.29            = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['53', '54'])).
% 11.05/11.29  thf('56', plain,
% 11.05/11.29      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29        | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['44', '55'])).
% 11.05/11.29  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('58', plain,
% 11.05/11.29      ((((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('demod', [status(thm)], ['56', '57'])).
% 11.05/11.29  thf('59', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D) != (k1_xboole_0))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('60', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('61', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.29      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.29  thf('62', plain,
% 11.05/11.29      ((((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 11.05/11.29  thf('63', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('64', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0)
% 11.05/11.29            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.29          | ((sk_D) = (sk_H))
% 11.05/11.29          | ((sk_D) = (k1_xboole_0))
% 11.05/11.29          | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['62', '63'])).
% 11.05/11.29  thf('65', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.29      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.29  thf('66', plain,
% 11.05/11.29      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_H) != (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['64', '65'])).
% 11.05/11.29  thf('67', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (((X0) != (k1_xboole_0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X0)
% 11.05/11.29          | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.29          | ((sk_D) = (sk_H))
% 11.05/11.29          | ((sk_D) = (k1_xboole_0))
% 11.05/11.29          | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['43', '66'])).
% 11.05/11.29  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('69', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (((X0) != (k1_xboole_0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X0)
% 11.05/11.29          | ((sk_D) = (sk_H))
% 11.05/11.29          | ((sk_D) = (k1_xboole_0))
% 11.05/11.29          | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('demod', [status(thm)], ['67', '68'])).
% 11.05/11.29  thf('70', plain,
% 11.05/11.29      ((((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (k1_xboole_0))
% 11.05/11.29        | ((sk_D) = (sk_H))
% 11.05/11.29        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 11.05/11.29      inference('simplify', [status(thm)], ['69'])).
% 11.05/11.29  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('72', plain,
% 11.05/11.29      ((((sk_H) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)) | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('simplify_reflect+', [status(thm)], ['70', '71'])).
% 11.05/11.29  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('74', plain,
% 11.05/11.29      (((v1_xboole_0 @ sk_D) | ((sk_D) = (sk_H)) | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['72', '73'])).
% 11.05/11.29  thf('75', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.29  thf('76', plain,
% 11.05/11.29      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf('77', plain,
% 11.05/11.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.05/11.29         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 11.05/11.29          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.05/11.29  thf('78', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 11.05/11.29          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['76', '77'])).
% 11.05/11.29  thf('79', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf('80', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup-', [status(thm)], ['78', '79'])).
% 11.05/11.29  thf('81', plain,
% 11.05/11.29      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.29  thf('82', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]:
% 11.05/11.29         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['80', '81'])).
% 11.05/11.29  thf('83', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('84', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup+', [status(thm)], ['82', '83'])).
% 11.05/11.29  thf('85', plain,
% 11.05/11.29      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 11.05/11.29        | ~ (v1_xboole_0 @ sk_D))),
% 11.05/11.29      inference('sup+', [status(thm)], ['75', '84'])).
% 11.05/11.29  thf('86', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.29      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.29  thf('87', plain, (~ (v1_xboole_0 @ sk_D)),
% 11.05/11.29      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 11.05/11.29  thf('88', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['74', '87'])).
% 11.05/11.29  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.29      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.29  thf('90', plain, (((v1_xboole_0 @ sk_H) | ((sk_D) = (sk_H)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['88', '89'])).
% 11.05/11.29  thf('91', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.29          | ~ (v1_xboole_0 @ X0))),
% 11.05/11.29      inference('sup+', [status(thm)], ['82', '83'])).
% 11.05/11.29  thf('92', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.29      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.29  thf('93', plain,
% 11.05/11.29      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_H))),
% 11.05/11.29      inference('sup-', [status(thm)], ['91', '92'])).
% 11.05/11.29  thf('94', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.29      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.29  thf('95', plain, (((sk_D) = (sk_H))),
% 11.05/11.29      inference('sup-', [status(thm)], ['90', '94'])).
% 11.05/11.29  thf('96', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['40', '95'])).
% 11.05/11.29  thf('97', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.29            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['37', '38'])).
% 11.05/11.29  thf('98', plain,
% 11.05/11.29      ((((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['96', '97'])).
% 11.05/11.29  thf('99', plain,
% 11.05/11.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.29           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.29      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.29  thf('100', plain,
% 11.05/11.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.29           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.29      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.29  thf('101', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 11.05/11.29      inference('sup+', [status(thm)], ['99', '100'])).
% 11.05/11.29  thf('102', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('103', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.29           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.29      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.29  thf('104', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['40', '95'])).
% 11.05/11.29  thf('105', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.29           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.29      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.29  thf(t37_mcart_1, axiom,
% 11.05/11.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.05/11.29     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 11.05/11.29       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 11.05/11.29         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 11.05/11.29  thf('106', plain,
% 11.05/11.29      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 11.05/11.29         (((k3_zfmisc_1 @ X16 @ X17 @ X18) = (k1_xboole_0))
% 11.05/11.29          | ((k3_zfmisc_1 @ X16 @ X17 @ X18) != (k3_zfmisc_1 @ X19 @ X20 @ X21))
% 11.05/11.29          | ((X17) = (X20)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t37_mcart_1])).
% 11.05/11.29  thf('107', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 11.05/11.29          | ((X1) = (X5))
% 11.05/11.29          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['105', '106'])).
% 11.05/11.29  thf('108', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.29           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.29      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.29  thf('109', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 11.05/11.29          | ((X1) = (X5))
% 11.05/11.29          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.29      inference('demod', [status(thm)], ['107', '108'])).
% 11.05/11.29  thf('110', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 11.05/11.29            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29          | ((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H) = (k1_xboole_0))
% 11.05/11.29          | ((sk_C) = (X1)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['104', '109'])).
% 11.05/11.29  thf('111', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['40', '95'])).
% 11.05/11.29  thf('112', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 11.05/11.29            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 11.05/11.29          | ((sk_C) = (X1)))),
% 11.05/11.29      inference('demod', [status(thm)], ['110', '111'])).
% 11.05/11.29  thf('113', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.29      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.29  thf('114', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 11.05/11.29            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29          | ((sk_C) = (X1)))),
% 11.05/11.29      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 11.05/11.29  thf('115', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.29         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 11.05/11.29            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.29          | ((sk_C) = (X1)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['103', '114'])).
% 11.05/11.29  thf('116', plain, (((sk_C) = (sk_G))),
% 11.05/11.29      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.29  thf('117', plain, (((sk_C) = (sk_G))),
% 11.05/11.29      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.29  thf('118', plain,
% 11.05/11.29      ((((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.29      inference('demod', [status(thm)], ['98', '116', '117'])).
% 11.05/11.29  thf('119', plain,
% 11.05/11.29      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 11.05/11.29          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['39', '118'])).
% 11.05/11.29  thf('120', plain,
% 11.05/11.29      ((((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 11.05/11.29            = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G)))),
% 11.05/11.29      inference('simplify', [status(thm)], ['119'])).
% 11.05/11.29  thf('121', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.29         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.29            = (k2_zfmisc_1 @ X2 @ X1))
% 11.05/11.29          | ((X0) = (k1_xboole_0))
% 11.05/11.29          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['34', '35'])).
% 11.05/11.29  thf('122', plain,
% 11.05/11.29      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))
% 11.05/11.29          = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((sk_H) = (k1_xboole_0))
% 11.05/11.29        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0))
% 11.05/11.29        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.29        | ((sk_G) = (k1_xboole_0)))),
% 11.05/11.29      inference('sup+', [status(thm)], ['120', '121'])).
% 11.05/11.29  thf('123', plain,
% 11.05/11.29      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf('124', plain,
% 11.05/11.29      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H)
% 11.05/11.29         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['40', '95'])).
% 11.05/11.29  thf('125', plain,
% 11.05/11.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.29         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.29           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.29      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.29  thf('126', plain,
% 11.05/11.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.05/11.29         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 11.05/11.29          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 11.05/11.29      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.05/11.29  thf('127', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.05/11.29         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.29          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['125', '126'])).
% 11.05/11.29  thf('128', plain,
% 11.05/11.29      (![X0 : $i]:
% 11.05/11.29         (~ (r2_hidden @ X0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29          | (r2_hidden @ (k1_mcart_1 @ X0) @ 
% 11.05/11.29             (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['124', '127'])).
% 11.05/11.29  thf('129', plain,
% 11.05/11.29      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.29        | (r2_hidden @ 
% 11.05/11.29           (k1_mcart_1 @ (sk_B @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) @ 
% 11.05/11.29           (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 11.05/11.29      inference('sup-', [status(thm)], ['123', '128'])).
% 11.05/11.29  thf('130', plain,
% 11.05/11.29      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.29      inference('demod', [status(thm)], ['28', '29'])).
% 11.05/11.29  thf('131', plain,
% 11.05/11.29      ((r2_hidden @ 
% 11.05/11.29        (k1_mcart_1 @ (sk_B @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) @ 
% 11.05/11.29        (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 11.05/11.29      inference('clc', [status(thm)], ['129', '130'])).
% 11.05/11.29  thf('132', plain,
% 11.05/11.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.29  thf('133', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 11.05/11.29      inference('sup-', [status(thm)], ['131', '132'])).
% 11.05/11.29  thf('134', plain, (((sk_C) = (sk_G))),
% 11.05/11.29      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.29  thf('135', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))),
% 11.05/11.30      inference('demod', [status(thm)], ['133', '134'])).
% 11.05/11.30  thf('136', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))
% 11.05/11.30            = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['122', '135'])).
% 11.05/11.30  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('138', plain,
% 11.05/11.30      ((((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))
% 11.05/11.30            = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('demod', [status(thm)], ['136', '137'])).
% 11.05/11.30  thf('139', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['36', '138'])).
% 11.05/11.30  thf('140', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['139'])).
% 11.05/11.30  thf('141', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['4', '5'])).
% 11.05/11.30  thf('142', plain,
% 11.05/11.30      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.05/11.30         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 11.05/11.30           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 11.05/11.30      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.05/11.30  thf('143', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['141', '142'])).
% 11.05/11.30  thf('144', plain,
% 11.05/11.30      (![X0 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30          | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['140', '143'])).
% 11.05/11.30  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('146', plain,
% 11.05/11.30      (![X0 : $i]:
% 11.05/11.30         (((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30          | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['144', '145'])).
% 11.05/11.30  thf('147', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('148', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['146', '147'])).
% 11.05/11.30  thf('149', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['148'])).
% 11.05/11.30  thf('150', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['37', '38'])).
% 11.05/11.30  thf('151', plain,
% 11.05/11.30      ((((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.30          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['96', '97'])).
% 11.05/11.30  thf('152', plain,
% 11.05/11.30      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X16 @ X17 @ X18) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ X16 @ X17 @ X18) != (k3_zfmisc_1 @ X19 @ X20 @ X21))
% 11.05/11.30          | ((X17) = (X20)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t37_mcart_1])).
% 11.05/11.30  thf('153', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.30            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (X1))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['151', '152'])).
% 11.05/11.30  thf('154', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((sk_B_1) = (X1))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.30              != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['153'])).
% 11.05/11.30  thf('155', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (X1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['150', '154'])).
% 11.05/11.30  thf('156', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((sk_B_1) = (X1))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['155'])).
% 11.05/11.30  thf('157', plain, (((sk_C) = (sk_G))),
% 11.05/11.30      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.30  thf('158', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((sk_B_1) = (X1))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['156', '157'])).
% 11.05/11.30  thf('159', plain,
% 11.05/11.30      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('eq_res', [status(thm)], ['158'])).
% 11.05/11.30  thf('160', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))),
% 11.05/11.30      inference('demod', [status(thm)], ['133', '134'])).
% 11.05/11.30  thf('161', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['159', '160'])).
% 11.05/11.30  thf('162', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('163', plain,
% 11.05/11.30      ((((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['161', '162'])).
% 11.05/11.30  thf('164', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['141', '142'])).
% 11.05/11.30  thf('165', plain,
% 11.05/11.30      (![X0 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (sk_F))
% 11.05/11.30          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['163', '164'])).
% 11.05/11.30  thf('166', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('167', plain,
% 11.05/11.30      (![X0 : $i]:
% 11.05/11.30         (((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (sk_F))
% 11.05/11.30          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['165', '166'])).
% 11.05/11.30  thf('168', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('169', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['167', '168'])).
% 11.05/11.30  thf('170', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['169'])).
% 11.05/11.30  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('172', plain, (((v1_xboole_0 @ sk_H) | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['170', '171'])).
% 11.05/11.30  thf('173', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.30      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.30  thf('174', plain, (((sk_B_1) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['172', '173'])).
% 11.05/11.30  thf('175', plain, (((sk_B_1) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['172', '173'])).
% 11.05/11.30  thf('176', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_F))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['149', '174', '175'])).
% 11.05/11.30  thf('177', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('178', plain,
% 11.05/11.30      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_A_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['176', '177'])).
% 11.05/11.30  thf('179', plain,
% 11.05/11.30      ((((sk_E) = (sk_A_1))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['33', '178'])).
% 11.05/11.30  thf('180', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (sk_A_1)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['179'])).
% 11.05/11.30  thf('181', plain,
% 11.05/11.30      ((((sk_A_1) != (sk_E))
% 11.05/11.30        | ((sk_B_1) != (sk_F))
% 11.05/11.30        | ((sk_C) != (sk_G))
% 11.05/11.30        | ((sk_D) != (sk_H)))),
% 11.05/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.05/11.30  thf('182', plain, ((((sk_A_1) != (sk_E))) <= (~ (((sk_A_1) = (sk_E))))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('183', plain, (((sk_D) = (sk_H))),
% 11.05/11.30      inference('sup-', [status(thm)], ['90', '94'])).
% 11.05/11.30  thf('184', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('185', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['183', '184'])).
% 11.05/11.30  thf('186', plain, ((((sk_D) = (sk_H)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['185'])).
% 11.05/11.30  thf('187', plain, (((sk_C) = (sk_G))),
% 11.05/11.30      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.30  thf('188', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('189', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['187', '188'])).
% 11.05/11.30  thf('190', plain, ((((sk_C) = (sk_G)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['189'])).
% 11.05/11.30  thf('191', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k2_zfmisc_1 @ X2 @ X1))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['34', '35'])).
% 11.05/11.30  thf('192', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.30           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.30      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.30  thf('193', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k2_zfmisc_1 @ X2 @ X1))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['34', '35'])).
% 11.05/11.30  thf('194', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1))
% 11.05/11.30          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0))
% 11.05/11.30          | ((X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['192', '193'])).
% 11.05/11.30  thf('195', plain,
% 11.05/11.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.30           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.30      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.30  thf('196', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 11.05/11.30          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0))
% 11.05/11.30          | ((X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['194', '195'])).
% 11.05/11.30  thf('197', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('198', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k2_relat_1 @ k1_xboole_0) = (X0))
% 11.05/11.30          | ((X3) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))
% 11.05/11.30              = (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['196', '197'])).
% 11.05/11.30  thf('199', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_H)
% 11.05/11.30         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.30      inference('demod', [status(thm)], ['40', '95'])).
% 11.05/11.30  thf('200', plain, (((sk_C) = (sk_G))),
% 11.05/11.30      inference('eq_res', [status(thm)], ['115'])).
% 11.05/11.30  thf('201', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G @ sk_H)
% 11.05/11.30         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 11.05/11.30      inference('demod', [status(thm)], ['199', '200'])).
% 11.05/11.30  thf('202', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k2_relat_1 @ k1_xboole_0) = (X0))
% 11.05/11.30          | ((X3) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))
% 11.05/11.30              = (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['196', '197'])).
% 11.05/11.30  thf('203', plain,
% 11.05/11.30      ((((k1_relat_1 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 11.05/11.30          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['201', '202'])).
% 11.05/11.30  thf('204', plain,
% 11.05/11.30      ((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 11.05/11.30          = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['198', '203'])).
% 11.05/11.30  thf('205', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G)
% 11.05/11.30            = (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_G)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['204'])).
% 11.05/11.30  thf('206', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30            = (k2_zfmisc_1 @ X2 @ X1))
% 11.05/11.30          | ((X0) = (k1_xboole_0))
% 11.05/11.30          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['34', '35'])).
% 11.05/11.30  thf('207', plain,
% 11.05/11.30      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))
% 11.05/11.30          = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['205', '206'])).
% 11.05/11.30  thf('208', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))
% 11.05/11.30            = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['207'])).
% 11.05/11.30  thf('209', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['191', '208'])).
% 11.05/11.30  thf('210', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['209'])).
% 11.05/11.30  thf('211', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('212', plain,
% 11.05/11.30      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['210', '211'])).
% 11.05/11.30  thf('213', plain,
% 11.05/11.30      ((r2_hidden @ 
% 11.05/11.30        (k1_mcart_1 @ (sk_B @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))) @ 
% 11.05/11.30        (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 11.05/11.30      inference('clc', [status(thm)], ['129', '130'])).
% 11.05/11.30  thf('214', plain,
% 11.05/11.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.30           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.30      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.30  thf('215', plain,
% 11.05/11.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.05/11.30         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 11.05/11.30          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.05/11.30  thf('216', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['214', '215'])).
% 11.05/11.30  thf('217', plain,
% 11.05/11.30      ((r2_hidden @ 
% 11.05/11.30        (k1_mcart_1 @ 
% 11.05/11.30         (k1_mcart_1 @ (sk_B @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)))) @ 
% 11.05/11.30        (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 11.05/11.30      inference('sup-', [status(thm)], ['213', '216'])).
% 11.05/11.30  thf('218', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.05/11.30  thf('219', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 11.05/11.30      inference('sup-', [status(thm)], ['217', '218'])).
% 11.05/11.30  thf('220', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['212', '219'])).
% 11.05/11.30  thf('221', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('222', plain,
% 11.05/11.30      ((((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1)))),
% 11.05/11.30      inference('demod', [status(thm)], ['220', '221'])).
% 11.05/11.30  thf('223', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('224', plain,
% 11.05/11.30      ((((sk_B_1) = (sk_F))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['222', '223'])).
% 11.05/11.30  thf('225', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['4', '5'])).
% 11.05/11.30  thf('226', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ X2))),
% 11.05/11.30      inference('sup+', [status(thm)], ['6', '7'])).
% 11.05/11.30  thf('227', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.30          | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ~ (v1_xboole_0 @ X2))),
% 11.05/11.30      inference('sup+', [status(thm)], ['225', '226'])).
% 11.05/11.30  thf('228', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('229', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 11.05/11.30      inference('demod', [status(thm)], ['227', '228'])).
% 11.05/11.30  thf('230', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.30           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.30      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.30  thf('231', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_xboole_0) = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['229', '230'])).
% 11.05/11.30  thf('232', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (sk_F))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['224', '231'])).
% 11.05/11.30  thf('233', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('234', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (sk_F))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['232', '233'])).
% 11.05/11.30  thf('235', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('236', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['234', '235'])).
% 11.05/11.30  thf('237', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['236'])).
% 11.05/11.30  thf('238', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['148'])).
% 11.05/11.30  thf('239', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('240', plain,
% 11.05/11.30      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['238', '239'])).
% 11.05/11.30  thf('241', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 11.05/11.30      inference('sup-', [status(thm)], ['217', '218'])).
% 11.05/11.30  thf('242', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['240', '241'])).
% 11.05/11.30  thf('243', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('244', plain,
% 11.05/11.30      ((((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_B_1)))),
% 11.05/11.30      inference('demod', [status(thm)], ['242', '243'])).
% 11.05/11.30  thf('245', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('246', plain,
% 11.05/11.30      ((((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['244', '245'])).
% 11.05/11.30  thf('247', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('248', plain,
% 11.05/11.30      ((((k2_relat_1 @ k1_xboole_0) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['246', '247'])).
% 11.05/11.30  thf('249', plain,
% 11.05/11.30      ((((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['248'])).
% 11.05/11.30  thf('250', plain,
% 11.05/11.30      ((((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['237', '249'])).
% 11.05/11.30  thf('251', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['250'])).
% 11.05/11.30  thf('252', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('253', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_B_1)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['251', '252'])).
% 11.05/11.30  thf('254', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['80', '81'])).
% 11.05/11.30  thf('255', plain,
% 11.05/11.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 11.05/11.30           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 11.05/11.30      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.05/11.30  thf('256', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('sup+', [status(thm)], ['254', '255'])).
% 11.05/11.30  thf('257', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 11.05/11.30      inference('sup-', [status(thm)], ['2', '3'])).
% 11.05/11.30  thf('258', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ X1)
% 11.05/11.30          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 11.05/11.30      inference('sup+', [status(thm)], ['256', '257'])).
% 11.05/11.30  thf('259', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('260', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('demod', [status(thm)], ['258', '259'])).
% 11.05/11.30  thf('261', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 11.05/11.30      inference('sup-', [status(thm)], ['131', '132'])).
% 11.05/11.30  thf('262', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 11.05/11.30      inference('sup-', [status(thm)], ['260', '261'])).
% 11.05/11.30  thf('263', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['253', '262'])).
% 11.05/11.30  thf('264', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('265', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_A_1)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['263', '264'])).
% 11.05/11.30  thf('266', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X2))),
% 11.05/11.30      inference('demod', [status(thm)], ['10', '15'])).
% 11.05/11.30  thf('267', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 11.05/11.30      inference('sup-', [status(thm)], ['131', '132'])).
% 11.05/11.30  thf('268', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 11.05/11.30      inference('sup-', [status(thm)], ['266', '267'])).
% 11.05/11.30  thf('269', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['265', '268'])).
% 11.05/11.30  thf('270', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('271', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_H)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['269', '270'])).
% 11.05/11.30  thf('272', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.30      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.30  thf('273', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['271', '272'])).
% 11.05/11.30  thf('274', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('275', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_G)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['273', '274'])).
% 11.05/11.30  thf('276', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['4', '5'])).
% 11.05/11.30  thf('277', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('sup+', [status(thm)], ['254', '255'])).
% 11.05/11.30  thf('278', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.30          | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('sup+', [status(thm)], ['276', '277'])).
% 11.05/11.30  thf('279', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('280', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('demod', [status(thm)], ['278', '279'])).
% 11.05/11.30  thf('281', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.05/11.30           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.05/11.30      inference('demod', [status(thm)], ['101', '102'])).
% 11.05/11.30  thf('282', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_xboole_0) = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('sup+', [status(thm)], ['280', '281'])).
% 11.05/11.30  thf('283', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('284', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_G))),
% 11.05/11.30      inference('sup-', [status(thm)], ['282', '283'])).
% 11.05/11.30  thf('285', plain, (~ (v1_xboole_0 @ sk_G)),
% 11.05/11.30      inference('simplify', [status(thm)], ['284'])).
% 11.05/11.30  thf('286', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['275', '285'])).
% 11.05/11.30  thf('287', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('288', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_F)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['286', '287'])).
% 11.05/11.30  thf('289', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 11.05/11.30      inference('demod', [status(thm)], ['258', '259'])).
% 11.05/11.30  thf('290', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['17', '18'])).
% 11.05/11.30  thf('291', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X1)
% 11.05/11.30          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['289', '290'])).
% 11.05/11.30  thf('292', plain,
% 11.05/11.30      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 11.05/11.30      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.05/11.30  thf('293', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ X2)
% 11.05/11.30          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['291', '292'])).
% 11.05/11.30  thf('294', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('295', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_F))),
% 11.05/11.30      inference('sup-', [status(thm)], ['293', '294'])).
% 11.05/11.30  thf('296', plain, (~ (v1_xboole_0 @ sk_F)),
% 11.05/11.30      inference('simplify', [status(thm)], ['295'])).
% 11.05/11.30  thf('297', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0)) | ((sk_B_1) = (sk_F)) | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['288', '296'])).
% 11.05/11.30  thf('298', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('299', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_E) | ((sk_G) = (sk_F)) | ((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['297', '298'])).
% 11.05/11.30  thf('300', plain, (~ (v1_xboole_0 @ sk_E)),
% 11.05/11.30      inference('sup-', [status(thm)], ['20', '30'])).
% 11.05/11.30  thf('301', plain, ((((sk_B_1) = (sk_F)) | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('clc', [status(thm)], ['299', '300'])).
% 11.05/11.30  thf('302', plain, ((((sk_B_1) != (sk_F))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('303', plain,
% 11.05/11.30      (((((sk_F) != (sk_F)) | ((sk_G) = (sk_F)))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['301', '302'])).
% 11.05/11.30  thf('304', plain, ((((sk_G) = (sk_F))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('simplify', [status(thm)], ['303'])).
% 11.05/11.30  thf('305', plain,
% 11.05/11.30      ((((sk_B_1) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k3_zfmisc_1 @ sk_E @ sk_F @ sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['161', '162'])).
% 11.05/11.30  thf('306', plain,
% 11.05/11.30      (((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_F) = (k1_xboole_0))
% 11.05/11.30         | ((sk_H) = (k1_xboole_0))
% 11.05/11.30         | ((sk_B_1) = (sk_F)))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup+', [status(thm)], ['304', '305'])).
% 11.05/11.30  thf('307', plain, ((((sk_B_1) != (sk_F))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('308', plain,
% 11.05/11.30      (((((k3_zfmisc_1 @ sk_E @ sk_F @ sk_F) = (k1_xboole_0))
% 11.05/11.30         | ((sk_H) = (k1_xboole_0)))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('simplify_reflect-', [status(thm)], ['306', '307'])).
% 11.05/11.30  thf('309', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['141', '142'])).
% 11.05/11.30  thf('310', plain,
% 11.05/11.30      ((![X0 : $i]:
% 11.05/11.30          (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30           | ((sk_H) = (k1_xboole_0))
% 11.05/11.30           | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ X0) = (k1_xboole_0))))
% 11.05/11.30         <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['308', '309'])).
% 11.05/11.30  thf('311', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('312', plain,
% 11.05/11.30      ((![X0 : $i]:
% 11.05/11.30          (((sk_H) = (k1_xboole_0))
% 11.05/11.30           | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ X0) = (k1_xboole_0))))
% 11.05/11.30         <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('demod', [status(thm)], ['310', '311'])).
% 11.05/11.30  thf('313', plain, ((((sk_G) = (sk_F))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('simplify', [status(thm)], ['303'])).
% 11.05/11.30  thf('314', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('315', plain,
% 11.05/11.30      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ sk_H) != (k1_xboole_0)))
% 11.05/11.30         <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['313', '314'])).
% 11.05/11.30  thf('316', plain,
% 11.05/11.30      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (k1_xboole_0))))
% 11.05/11.30         <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup-', [status(thm)], ['312', '315'])).
% 11.05/11.30  thf('317', plain, ((((sk_H) = (k1_xboole_0))) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('simplify', [status(thm)], ['316'])).
% 11.05/11.30  thf('318', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('319', plain, (((v1_xboole_0 @ sk_H)) <= (~ (((sk_B_1) = (sk_F))))),
% 11.05/11.30      inference('sup+', [status(thm)], ['317', '318'])).
% 11.05/11.30  thf('320', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.30      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.30  thf('321', plain, ((((sk_B_1) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['319', '320'])).
% 11.05/11.30  thf('322', plain,
% 11.05/11.30      (~ (((sk_A_1) = (sk_E))) | ~ (((sk_B_1) = (sk_F))) | 
% 11.05/11.30       ~ (((sk_C) = (sk_G))) | ~ (((sk_D) = (sk_H)))),
% 11.05/11.30      inference('split', [status(esa)], ['181'])).
% 11.05/11.30  thf('323', plain, (~ (((sk_A_1) = (sk_E)))),
% 11.05/11.30      inference('sat_resolution*', [status(thm)], ['186', '190', '321', '322'])).
% 11.05/11.30  thf('324', plain, (((sk_A_1) != (sk_E))),
% 11.05/11.30      inference('simpl_trail', [status(thm)], ['182', '323'])).
% 11.05/11.30  thf('325', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify_reflect-', [status(thm)], ['180', '324'])).
% 11.05/11.30  thf('326', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 11.05/11.30      inference('sup-', [status(thm)], ['217', '218'])).
% 11.05/11.30  thf('327', plain, (((sk_B_1) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['172', '173'])).
% 11.05/11.30  thf('328', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A_1 @ sk_F))),
% 11.05/11.30      inference('demod', [status(thm)], ['326', '327'])).
% 11.05/11.30  thf('329', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['325', '328'])).
% 11.05/11.30  thf('330', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('331', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['329', '330'])).
% 11.05/11.30  thf('332', plain,
% 11.05/11.30      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['209'])).
% 11.05/11.30  thf('333', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('334', plain,
% 11.05/11.30      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_A_1))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['332', '333'])).
% 11.05/11.30  thf('335', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 11.05/11.30      inference('sup-', [status(thm)], ['217', '218'])).
% 11.05/11.30  thf('336', plain,
% 11.05/11.30      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_A_1)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['334', '335'])).
% 11.05/11.30  thf('337', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('338', plain,
% 11.05/11.30      ((((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (sk_A_1)))),
% 11.05/11.30      inference('demod', [status(thm)], ['336', '337'])).
% 11.05/11.30  thf('339', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X4))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('340', plain,
% 11.05/11.30      ((((sk_A_1) = (sk_E))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['338', '339'])).
% 11.05/11.30  thf('341', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_xboole_0) = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['229', '230'])).
% 11.05/11.30  thf('342', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (sk_E))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['340', '341'])).
% 11.05/11.30  thf('343', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('344', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((sk_G) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (sk_E))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['342', '343'])).
% 11.05/11.30  thf('345', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('346', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (sk_E))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['344', '345'])).
% 11.05/11.30  thf('347', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_B_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (sk_E)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['346'])).
% 11.05/11.30  thf('348', plain, (((sk_B_1) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['172', '173'])).
% 11.05/11.30  thf('349', plain,
% 11.05/11.30      ((((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (sk_E)))),
% 11.05/11.30      inference('demod', [status(thm)], ['347', '348'])).
% 11.05/11.30  thf('350', plain,
% 11.05/11.30      ((((sk_A_1) = (sk_E))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['349'])).
% 11.05/11.30  thf('351', plain, (((sk_A_1) != (sk_E))),
% 11.05/11.30      inference('simpl_trail', [status(thm)], ['182', '323'])).
% 11.05/11.30  thf('352', plain,
% 11.05/11.30      ((((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_G))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify_reflect-', [status(thm)], ['350', '351'])).
% 11.05/11.30  thf('353', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['329', '330'])).
% 11.05/11.30  thf('354', plain,
% 11.05/11.30      (![X4 : $i, X5 : $i]:
% 11.05/11.30         (((X4) = (k1_xboole_0))
% 11.05/11.30          | ((k2_relat_1 @ (k2_zfmisc_1 @ X4 @ X5)) = (X5))
% 11.05/11.30          | ((X5) = (k1_xboole_0)))),
% 11.05/11.30      inference('cnf', [status(esa)], [t195_relat_1])).
% 11.05/11.30  thf('355', plain,
% 11.05/11.30      ((((k2_relat_1 @ k1_xboole_0) = (sk_F))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['353', '354'])).
% 11.05/11.30  thf('356', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_relat_1 @ k1_xboole_0) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['355'])).
% 11.05/11.30  thf('357', plain,
% 11.05/11.30      ((((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['352', '356'])).
% 11.05/11.30  thf('358', plain,
% 11.05/11.30      ((((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['357'])).
% 11.05/11.30  thf('359', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('360', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_A_1)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['358', '359'])).
% 11.05/11.30  thf('361', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 11.05/11.30      inference('sup-', [status(thm)], ['266', '267'])).
% 11.05/11.30  thf('362', plain,
% 11.05/11.30      ((((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['360', '361'])).
% 11.05/11.30  thf('363', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('364', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_H)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['362', '363'])).
% 11.05/11.30  thf('365', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.30      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.30  thf('366', plain,
% 11.05/11.30      ((((sk_G) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['364', '365'])).
% 11.05/11.30  thf('367', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('368', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_G)
% 11.05/11.30        | ((sk_G) = (sk_F))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['366', '367'])).
% 11.05/11.30  thf('369', plain, (~ (v1_xboole_0 @ sk_G)),
% 11.05/11.30      inference('simplify', [status(thm)], ['284'])).
% 11.05/11.30  thf('370', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)) | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['368', '369'])).
% 11.05/11.30  thf('371', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('372', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_F) | ((sk_G) = (sk_F)) | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['370', '371'])).
% 11.05/11.30  thf('373', plain, (~ (v1_xboole_0 @ sk_F)),
% 11.05/11.30      inference('simplify', [status(thm)], ['295'])).
% 11.05/11.30  thf('374', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('clc', [status(thm)], ['372', '373'])).
% 11.05/11.30  thf('375', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('376', plain, (((v1_xboole_0 @ sk_E) | ((sk_G) = (sk_F)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['374', '375'])).
% 11.05/11.30  thf('377', plain, (~ (v1_xboole_0 @ sk_E)),
% 11.05/11.30      inference('sup-', [status(thm)], ['20', '30'])).
% 11.05/11.30  thf('378', plain, (((sk_G) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['376', '377'])).
% 11.05/11.30  thf('379', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['331', '378'])).
% 11.05/11.30  thf('380', plain,
% 11.05/11.30      ((((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['379'])).
% 11.05/11.30  thf('381', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.05/11.30         (((k1_xboole_0) = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 11.05/11.30          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['229', '230'])).
% 11.05/11.30  thf('382', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.05/11.30          | ((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['380', '381'])).
% 11.05/11.30  thf('383', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('384', plain,
% 11.05/11.30      (![X0 : $i, X1 : $i]:
% 11.05/11.30         (((sk_F) = (k1_xboole_0))
% 11.05/11.30          | ((sk_E) = (k1_xboole_0))
% 11.05/11.30          | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30          | ((sk_H) = (k1_xboole_0))
% 11.05/11.30          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)))),
% 11.05/11.30      inference('demod', [status(thm)], ['382', '383'])).
% 11.05/11.30  thf('385', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['59', '60'])).
% 11.05/11.30  thf('386', plain, (((sk_G) = (sk_F))),
% 11.05/11.30      inference('clc', [status(thm)], ['376', '377'])).
% 11.05/11.30  thf('387', plain,
% 11.05/11.30      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_F @ sk_H) != (k1_xboole_0))),
% 11.05/11.30      inference('demod', [status(thm)], ['385', '386'])).
% 11.05/11.30  thf('388', plain,
% 11.05/11.30      ((((k1_xboole_0) != (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['384', '387'])).
% 11.05/11.30  thf('389', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_A_1) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('simplify', [status(thm)], ['388'])).
% 11.05/11.30  thf('390', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('391', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_A_1)
% 11.05/11.30        | ((sk_H) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['389', '390'])).
% 11.05/11.30  thf('392', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 11.05/11.30      inference('sup-', [status(thm)], ['266', '267'])).
% 11.05/11.30  thf('393', plain,
% 11.05/11.30      ((((sk_F) = (k1_xboole_0))
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_H) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup-', [status(thm)], ['391', '392'])).
% 11.05/11.30  thf('394', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('395', plain,
% 11.05/11.30      (((v1_xboole_0 @ sk_H)
% 11.05/11.30        | ((sk_E) = (k1_xboole_0))
% 11.05/11.30        | ((sk_F) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['393', '394'])).
% 11.05/11.30  thf('396', plain, (~ (v1_xboole_0 @ sk_H)),
% 11.05/11.30      inference('simplify', [status(thm)], ['93'])).
% 11.05/11.30  thf('397', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('clc', [status(thm)], ['395', '396'])).
% 11.05/11.30  thf('398', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.05/11.30      inference('demod', [status(thm)], ['11', '14'])).
% 11.05/11.30  thf('399', plain, (((v1_xboole_0 @ sk_F) | ((sk_E) = (k1_xboole_0)))),
% 11.05/11.30      inference('sup+', [status(thm)], ['397', '398'])).
% 11.05/11.30  thf('400', plain, (~ (v1_xboole_0 @ sk_F)),
% 11.05/11.30      inference('simplify', [status(thm)], ['295'])).
% 11.05/11.30  thf('401', plain, (((sk_E) = (k1_xboole_0))),
% 11.05/11.30      inference('clc', [status(thm)], ['399', '400'])).
% 11.05/11.30  thf('402', plain, ((v1_xboole_0 @ sk_E)),
% 11.05/11.30      inference('demod', [status(thm)], ['32', '401'])).
% 11.05/11.30  thf('403', plain, ($false), inference('demod', [status(thm)], ['31', '402'])).
% 11.05/11.30  
% 11.05/11.30  % SZS output end Refutation
% 11.05/11.30  
% 11.05/11.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
