%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zkKXY8gwp1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 176 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :   20
%              Number of atoms          :  654 (1469 expanded)
%              Number of equality atoms :   22 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X20 ) )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('2',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ( X19
        = ( k1_wellord1 @ ( k1_wellord2 @ X18 ) @ X19 ) )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
       != ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('8',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X7 @ X8 ) @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X22 ) @ X21 )
        = ( k1_wellord2 @ X21 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ ( k3_relat_1 @ X0 ) ) @ ( k1_wellord1 @ X0 @ X1 ) )
        = ( k1_wellord2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
        = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ~ ( r4_wellord1 @ X11 @ ( k2_wellord1 @ X11 @ ( k1_wellord1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X20 ) )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('46',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r4_wellord1 @ X9 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('50',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('51',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('66',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['43','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zkKXY8gwp1
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 47 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.48  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.48  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(t7_wellord2, axiom,
% 0.20/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X20 : $i]:
% 0.20/0.48         ((v2_wellord1 @ (k1_wellord2 @ X20)) | ~ (v3_ordinal1 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.48  thf(t26_ordinal1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.48           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X5)
% 0.20/0.48          | (r1_ordinal1 @ X6 @ X5)
% 0.20/0.48          | (r2_hidden @ X5 @ X6)
% 0.20/0.48          | ~ (v3_ordinal1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.48  thf(t11_wellord2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.48           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.48             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.48              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.48                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X5)
% 0.20/0.48          | (r1_ordinal1 @ X6 @ X5)
% 0.20/0.48          | (r2_hidden @ X5 @ X6)
% 0.20/0.48          | ~ (v3_ordinal1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.48  thf(t10_wellord2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.48           ( ( r2_hidden @ A @ B ) =>
% 0.20/0.48             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X18)
% 0.20/0.48          | ((X19) = (k1_wellord1 @ (k1_wellord2 @ X18) @ X19))
% 0.20/0.48          | ~ (r2_hidden @ X19 @ X18)
% 0.20/0.48          | ~ (v3_ordinal1 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X0)
% 0.20/0.48          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.48          | ~ (v3_ordinal1 @ X1)
% 0.20/0.48          | ~ (v3_ordinal1 @ X1)
% 0.20/0.48          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.48          | ~ (v3_ordinal1 @ X1)
% 0.20/0.48          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.48  thf(d1_wellord2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.48         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48           ( ![C:$i,D:$i]:
% 0.20/0.48             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.48               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.48                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (((X14) != (k1_wellord2 @ X13))
% 0.20/0.48          | ((k3_relat_1 @ X14) = (X13))
% 0.20/0.48          | ~ (v1_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X13 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ (k1_wellord2 @ X13))
% 0.20/0.48          | ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.48  thf('9', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.48  thf('10', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(t13_wellord1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_wellord1 @ X7 @ X8) @ (k3_relat_1 @ X7))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.20/0.48  thf(t8_wellord2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         (((k2_wellord1 @ (k1_wellord2 @ X22) @ X21) = (k1_wellord2 @ X21))
% 0.20/0.48          | ~ (r1_tarski @ X21 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k2_wellord1 @ (k1_wellord2 @ (k3_relat_1 @ X0)) @ 
% 0.20/0.48              (k1_wellord1 @ X0 @ X1))
% 0.20/0.48              = (k1_wellord2 @ (k1_wellord1 @ X0 @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.48            (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.48            = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)))
% 0.20/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf('15', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.48           (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.48           = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf(t57_wellord1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( v2_wellord1 @ A ) =>
% 0.20/0.48         ( ![B:$i]:
% 0.20/0.48           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.48                ( r4_wellord1 @
% 0.20/0.48                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (v2_wellord1 @ X11)
% 0.20/0.48          | ~ (r4_wellord1 @ X11 @ 
% 0.20/0.48               (k2_wellord1 @ X11 @ (k1_wellord1 @ X11 @ X12)))
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.48             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.48  thf('20', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.48             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.20/0.48          | ~ (v3_ordinal1 @ X1)
% 0.20/0.48          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.48          | ~ (v3_ordinal1 @ X0)
% 0.20/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.48        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '22'])).
% 0.20/0.48  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.48        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.48        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.48        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '26'])).
% 0.20/0.48  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.48        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A)) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  thf('32', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '31'])).
% 0.20/0.48  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.48       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X3)
% 0.20/0.48          | ~ (v3_ordinal1 @ X4)
% 0.20/0.48          | (r1_tarski @ X3 @ X4)
% 0.20/0.48          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i]:
% 0.20/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('41', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X20 : $i]:
% 0.20/0.48         ((v2_wellord1 @ (k1_wellord2 @ X20)) | ~ (v3_ordinal1 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X5)
% 0.20/0.48          | (r1_ordinal1 @ X6 @ X5)
% 0.20/0.48          | (r2_hidden @ X5 @ X6)
% 0.20/0.48          | ~ (v3_ordinal1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t50_wellord1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X9)
% 0.20/0.48          | (r4_wellord1 @ X9 @ X10)
% 0.20/0.48          | ~ (r4_wellord1 @ X10 @ X9)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.48        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.48        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.48  thf('50', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.20/0.48          | ~ (v3_ordinal1 @ X1)
% 0.20/0.48          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.48          | ~ (v3_ordinal1 @ X0)
% 0.20/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.48        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.48        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.48        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.48        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '56'])).
% 0.20/0.48  thf('58', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.48        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.48  thf('62', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '61'])).
% 0.20/0.48  thf('63', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (v3_ordinal1 @ X3)
% 0.20/0.48          | ~ (v3_ordinal1 @ X4)
% 0.20/0.48          | (r1_tarski @ X3 @ X4)
% 0.20/0.48          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.48        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.48  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.20/0.48  thf('70', plain, ($false), inference('demod', [status(thm)], ['43', '69'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
