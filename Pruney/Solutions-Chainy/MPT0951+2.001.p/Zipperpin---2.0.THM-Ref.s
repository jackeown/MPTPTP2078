%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z44J6hbvB0

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  759 (1804 expanded)
%              Number of equality atoms :   28 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_wellord2_type,type,(
    r2_wellord2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t22_wellord2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_wellord2 @ A @ B )
        & ( r2_wellord2 @ B @ C ) )
     => ( r2_wellord2 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_wellord2 @ A @ B )
          & ( r2_wellord2 @ B @ C ) )
       => ( r2_wellord2 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t22_wellord2])).

thf('0',plain,(
    ~ ( r2_wellord2 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(fc7_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B )
        & ( v2_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v2_funct_1 @ X11 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('5',plain,(
    r2_wellord2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_wellord2 @ A @ B )
    <=> ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = B )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v2_funct_1 @ C )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X12 @ X13 ) )
        = X13 )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('7',plain,
    ( ( k1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_wellord2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X12 @ X13 ) )
        = X12 )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('10',plain,
    ( ( k2_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X0 ) )
        = ( k1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_wellord2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('15',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_wellord2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X12 @ X13 ) )
        = X13 )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('18',plain,
    ( ( k1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X0 ) )
        = sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_wellord2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('25',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['20','22','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_wellord2 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
       != X13 )
      | ( ( k2_relat_1 @ X15 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('28',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ( r2_wellord2 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    r2_wellord2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('33',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('36',plain,(
    r2_wellord2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('38',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['30','33','34','35','38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    r2_wellord2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_funct_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('43',plain,(
    v2_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('45',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('48',plain,(
    r2_wellord2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_funct_1 @ ( sk_C @ X12 @ X13 ) )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('50',plain,(
    v2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','43','44','45','46','47','50'])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','51'])).

thf('53',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('54',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('55',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('56',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('57',plain,(
    r2_wellord2 @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( r2_wellord2 @ sk_A @ ( k9_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k2_relat_1 @ ( sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('60',plain,
    ( ( k1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('62',plain,
    ( ( ( k9_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k2_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_wellord2 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X12 @ X13 ) )
        = X12 )
      | ~ ( r2_wellord2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord2])).

thf('65',plain,
    ( ( k2_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('67',plain,
    ( ( k9_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['62','65','66'])).

thf('68',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('69',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('70',plain,(
    r2_wellord2 @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['58','59','67','68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z44J6hbvB0
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 64 iterations in 0.066s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_wellord2_type, type, r2_wellord2: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(t22_wellord2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_wellord2 @ A @ B ) & ( r2_wellord2 @ B @ C ) ) =>
% 0.20/0.52       ( r2_wellord2 @ A @ C ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( ( r2_wellord2 @ A @ B ) & ( r2_wellord2 @ B @ C ) ) =>
% 0.20/0.52          ( r2_wellord2 @ A @ C ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t22_wellord2])).
% 0.20/0.52  thf('0', plain, (~ (r2_wellord2 @ sk_A @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t160_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ B ) =>
% 0.20/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.52             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X4)
% 0.20/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.20/0.52              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.20/0.52          | ~ (v1_relat_1 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.20/0.52  thf(fc2_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.20/0.52         ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.20/0.52         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X9)
% 0.20/0.52          | ~ (v1_funct_1 @ X9)
% 0.20/0.52          | (v1_funct_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.52  thf(fc7_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) & 
% 0.20/0.52         ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.20/0.52         ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X10)
% 0.20/0.52          | ~ (v1_funct_1 @ X10)
% 0.20/0.52          | ~ (v1_relat_1 @ X10)
% 0.20/0.52          | ~ (v1_relat_1 @ X11)
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v2_funct_1 @ X11)
% 0.20/0.52          | (v2_funct_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc7_funct_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X9)
% 0.20/0.52          | ~ (v1_funct_1 @ X9)
% 0.20/0.52          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.52  thf('5', plain, ((r2_wellord2 @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d4_wellord2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_wellord2 @ A @ B ) <=>
% 0.20/0.52       ( ?[C:$i]:
% 0.20/0.52         ( ( ( k2_relat_1 @ C ) = ( B ) ) & ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.52           ( v2_funct_1 @ C ) & ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (sk_C @ X12 @ X13)) = (X13))
% 0.20/0.52          | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('7', plain, (((k1_relat_1 @ (sk_C @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain, ((r2_wellord2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (sk_C @ X12 @ X13)) = (X12))
% 0.20/0.52          | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('10', plain, (((k2_relat_1 @ (sk_C @ sk_B @ sk_A)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(t46_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ B ) =>
% 0.20/0.52           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.52             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X6)
% 0.20/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6)) = (k1_relat_1 @ X7))
% 0.20/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X6))
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r1_tarski @ sk_B @ (k1_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ X0))
% 0.20/0.52              = (k1_relat_1 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, ((r2_wellord2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('15', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain, ((r2_wellord2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (sk_C @ X12 @ X13)) = (X13))
% 0.20/0.52          | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('18', plain, (((k1_relat_1 @ (sk_C @ sk_B @ sk_A)) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r1_tarski @ sk_B @ (k1_relat_1 @ X0))
% 0.20/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ X0)) = (sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '15', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ((k1_relat_1 @ 
% 0.20/0.52            (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52            = (sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '19'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain, ((r2_wellord2 @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('25', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((k1_relat_1 @ 
% 0.20/0.52         (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))) = (
% 0.20/0.52         sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '22', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         ((r2_wellord2 @ X13 @ X14)
% 0.20/0.52          | ~ (v1_relat_1 @ X15)
% 0.20/0.52          | ~ (v1_funct_1 @ X15)
% 0.20/0.52          | ~ (v2_funct_1 @ X15)
% 0.20/0.52          | ((k1_relat_1 @ X15) != (X13))
% 0.20/0.52          | ((k2_relat_1 @ X15) != (X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X15 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X15)
% 0.20/0.52          | ~ (v1_funct_1 @ X15)
% 0.20/0.52          | ~ (v1_relat_1 @ X15)
% 0.20/0.52          | (r2_wellord2 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r2_wellord2 @ sk_A @ 
% 0.20/0.52         (k2_relat_1 @ 
% 0.20/0.52          (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))
% 0.20/0.52        | ~ (v1_relat_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | ~ (v2_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['26', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v2_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | (r2_wellord2 @ sk_A @ 
% 0.20/0.52           (k2_relat_1 @ 
% 0.20/0.52            (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '29'])).
% 0.20/0.52  thf('31', plain, ((r2_wellord2 @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('33', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('35', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('36', plain, ((r2_wellord2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('38', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (v2_funct_1 @ 
% 0.20/0.52           (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | (r2_wellord2 @ sk_A @ 
% 0.20/0.52           (k2_relat_1 @ 
% 0.20/0.52            (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '33', '34', '35', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (v2_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v2_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | (r2_wellord2 @ sk_A @ 
% 0.20/0.52           (k2_relat_1 @ 
% 0.20/0.52            (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))
% 0.20/0.52        | ~ (v1_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '39'])).
% 0.20/0.52  thf('41', plain, ((r2_wellord2 @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v2_funct_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('43', plain, ((v2_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('45', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('46', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('47', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('48', plain, ((r2_wellord2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v2_funct_1 @ (sk_C @ X12 @ X13)) | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('50', plain, ((v2_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((r2_wellord2 @ sk_A @ 
% 0.20/0.52         (k2_relat_1 @ 
% 0.20/0.52          (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))
% 0.20/0.52        | ~ (v1_funct_1 @ 
% 0.20/0.52             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['40', '43', '44', '45', '46', '47', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | (r2_wellord2 @ sk_A @ 
% 0.20/0.52           (k2_relat_1 @ 
% 0.20/0.52            (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '51'])).
% 0.20/0.52  thf('53', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('54', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('55', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('56', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((r2_wellord2 @ sk_A @ 
% 0.20/0.52        (k2_relat_1 @ 
% 0.20/0.52         (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (((r2_wellord2 @ sk_A @ 
% 0.20/0.52         (k9_relat_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.52          (k2_relat_1 @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['1', '57'])).
% 0.20/0.52  thf('59', plain, (((k2_relat_1 @ (sk_C @ sk_B @ sk_A)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('60', plain, (((k1_relat_1 @ (sk_C @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t146_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X3 : $i]:
% 0.20/0.52         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.20/0.52          | ~ (v1_relat_1 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((((k9_relat_1 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.20/0.52          = (k2_relat_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain, ((r2_wellord2 @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (sk_C @ X12 @ X13)) = (X12))
% 0.20/0.52          | ~ (r2_wellord2 @ X13 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_wellord2])).
% 0.20/0.52  thf('65', plain, (((k2_relat_1 @ (sk_C @ sk_C_1 @ sk_B)) = (sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('67', plain, (((k9_relat_1 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B) = (sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '65', '66'])).
% 0.20/0.52  thf('68', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('69', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('70', plain, ((r2_wellord2 @ sk_A @ sk_C_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['58', '59', '67', '68', '69'])).
% 0.20/0.52  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
