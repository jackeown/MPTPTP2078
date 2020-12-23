%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRtR9o1bWY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:28 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  219 (2486 expanded)
%              Number of leaves         :   28 ( 748 expanded)
%              Depth                    :   55
%              Number of atoms          : 1690 (23319 expanded)
%              Number of equality atoms :   72 (1364 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

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

thf('3',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_B @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ( sk_A = sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( sk_A = sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
      = ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

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

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('40',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','42'])).

thf('44',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
      = ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) )
      | ( r2_hidden @ X9 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('65',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('66',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('71',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('76',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r4_wellord1 @ X12 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('85',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('86',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ X16 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('91',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('95',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('97',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('98',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','80','95','96','97'])).

thf('99',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('100',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','100'])).

thf('102',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('105',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('114',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) )
      | ( r2_hidden @ X9 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('121',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('122',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('127',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('128',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('129',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','42'])).

thf('131',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('133',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['126','137'])).

thf('139',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_B = sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','140'])).

thf('142',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('148',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) )
      | ( r2_hidden @ X9 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('151',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('152',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference(eq_fact,[status(thm)],['154'])).

thf('156',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('159',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('164',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('166',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('168',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ X16 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('171',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','172'])).

thf('174',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('175',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('177',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('178',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165','175','176','177'])).

thf('179',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('180',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','180'])).

thf('182',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('185',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    $false ),
    inference(demod,[status(thm)],['112','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRtR9o1bWY
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 176 iterations in 0.222s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.46/0.70  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.46/0.70  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.46/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.46/0.70  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.46/0.70  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.46/0.70  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.46/0.70  thf(t7_wellord2, axiom,
% 0.46/0.70    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X26 : $i]:
% 0.46/0.70         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.70  thf(t24_ordinal1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.70           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.46/0.70                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X7)
% 0.46/0.70          | (r2_hidden @ X8 @ X7)
% 0.46/0.70          | ((X8) = (X7))
% 0.46/0.70          | (r2_hidden @ X7 @ X8)
% 0.46/0.70          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.70      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X26 : $i]:
% 0.46/0.70         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.70  thf(t11_wellord2, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.70           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.46/0.70             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( v3_ordinal1 @ A ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( v3_ordinal1 @ B ) =>
% 0.46/0.70              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.46/0.70                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.46/0.70  thf('3', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(connectedness_r1_ordinal1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.46/0.70       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X3 : $i, X4 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X3)
% 0.46/0.70          | ~ (v3_ordinal1 @ X4)
% 0.46/0.70          | (r1_ordinal1 @ X3 @ X4)
% 0.46/0.70          | (r1_ordinal1 @ X4 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.46/0.70  thf(redefinition_r1_ordinal1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.46/0.70       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X5)
% 0.46/0.70          | ~ (v3_ordinal1 @ X6)
% 0.46/0.70          | (r1_tarski @ X5 @ X6)
% 0.46/0.70          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((r1_ordinal1 @ X0 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | (r1_tarski @ X1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((r1_tarski @ X1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ X1))),
% 0.46/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_ordinal1 @ sk_B @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_tarski @ X0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '7'])).
% 0.46/0.70  thf('9', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X3 : $i, X4 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X3)
% 0.46/0.70          | ~ (v3_ordinal1 @ X4)
% 0.46/0.70          | (r1_ordinal1 @ X3 @ X4)
% 0.46/0.70          | (r1_ordinal1 @ X4 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X5)
% 0.46/0.70          | ~ (v3_ordinal1 @ X6)
% 0.46/0.70          | (r1_tarski @ X5 @ X6)
% 0.46/0.70          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.70          | (r1_tarski @ X0 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.70          | (r1_tarski @ X0 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_tarski @ X0 @ sk_A)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.70  thf(d10_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X0 : $i, X2 : $i]:
% 0.46/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.70          | ~ (r1_tarski @ sk_A @ X0)
% 0.46/0.70          | ((sk_A) = (X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      ((~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ((sk_A) = (sk_B))
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '18'])).
% 0.46/0.70  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ((sk_A) = (sk_B))
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.46/0.70  thf('23', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X5)
% 0.46/0.70          | ~ (v3_ordinal1 @ X6)
% 0.46/0.70          | (r1_tarski @ X5 @ X6)
% 0.46/0.70          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | (r1_tarski @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('29', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.46/0.70  thf(t8_wellord2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.70       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.70          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X7)
% 0.46/0.70          | (r2_hidden @ X8 @ X7)
% 0.46/0.70          | ((X8) = (X7))
% 0.46/0.70          | (r2_hidden @ X7 @ X8)
% 0.46/0.70          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.70      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.46/0.70  thf(t10_wellord2, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.70           ( ( r2_hidden @ A @ B ) =>
% 0.46/0.70             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X24 : $i, X25 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X24)
% 0.46/0.70          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.70          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.70          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X1)
% 0.46/0.70          | (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ((X1) = (X0))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ((X1) = (X0))
% 0.46/0.70          | (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1))),
% 0.46/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.70  thf(t57_wellord1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ( v2_wellord1 @ A ) =>
% 0.46/0.70         ( ![B:$i]:
% 0.46/0.70           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.46/0.70                ( r4_wellord1 @
% 0.46/0.70                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         (~ (v2_wellord1 @ X17)
% 0.46/0.70          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.70               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.70          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.70             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ X1 @ X0)
% 0.46/0.70          | ((X0) = (X1))
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.46/0.70          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.46/0.70          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.70  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.46/0.70  thf('38', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf(d1_wellord2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.46/0.70         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.70           ( ![C:$i,D:$i]:
% 0.46/0.70             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.46/0.70               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.46/0.70                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (((X20) != (k1_wellord2 @ X19))
% 0.46/0.70          | ((k3_relat_1 @ X20) = (X19))
% 0.46/0.70          | ~ (v1_relat_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X19 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.46/0.70          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.70  thf('41', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('42', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.70             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ X1 @ X0)
% 0.46/0.70          | ((X0) = (X1))
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ~ (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['37', '38', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | ((sk_B) = (sk_A))
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['31', '43'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | ((sk_B) = (sk_A))
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.46/0.70  thf('49', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      ((~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '50'])).
% 0.46/0.70  thf('52', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (((r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ((sk_B) = (sk_A))
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '53'])).
% 0.46/0.70  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('56', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (((r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ((sk_B) = (sk_A))
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ((sk_B) = (sk_A))
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.70  thf('59', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('60', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf(t19_wellord1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ C ) =>
% 0.46/0.70       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.46/0.70         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X9 @ (k3_relat_1 @ (k2_wellord1 @ X10 @ X11)))
% 0.46/0.70          | (r2_hidden @ X9 @ (k3_relat_1 @ X10))
% 0.46/0.70          | ~ (v1_relat_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70          | (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('64', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('65', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('66', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.70          | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70          | (r2_hidden @ X0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_A @ sk_A)
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['60', '67'])).
% 0.46/0.70  thf('69', plain, (((r2_hidden @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify', [status(thm)], ['68'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (![X24 : $i, X25 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X24)
% 0.46/0.70          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.70          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.70          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_A))
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('73', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.46/0.70  thf('75', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         (~ (v2_wellord1 @ X17)
% 0.46/0.70          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.70               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.70          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ 
% 0.46/0.70           (k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_A))
% 0.46/0.70        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_A)))
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('78', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.70      inference('simplify', [status(thm)], ['77'])).
% 0.46/0.70  thf('79', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.70          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.70  thf('80', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t50_wellord1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v1_relat_1 @ B ) =>
% 0.46/0.70           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X12)
% 0.46/0.70          | (r4_wellord1 @ X12 @ X13)
% 0.46/0.70          | ~ (r4_wellord1 @ X13 @ X12)
% 0.46/0.70          | ~ (v1_relat_1 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.70  thf('84', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('85', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('86', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.70  thf('87', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t52_wellord1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v1_relat_1 @ B ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( v1_relat_1 @ C ) =>
% 0.46/0.70               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.46/0.70                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.46/0.70  thf('88', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X14)
% 0.46/0.70          | ~ (r4_wellord1 @ X15 @ X14)
% 0.46/0.70          | ~ (r4_wellord1 @ X14 @ X16)
% 0.46/0.70          | (r4_wellord1 @ X15 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.46/0.70  thf('89', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.46/0.70          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.70  thf('90', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('91', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('92', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0)
% 0.46/0.70          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.46/0.70          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.46/0.70  thf('93', plain,
% 0.46/0.70      (((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['86', '92'])).
% 0.46/0.70  thf('94', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('95', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.70  thf('96', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('97', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('98', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ sk_A)
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['76', '80', '95', '96', '97'])).
% 0.46/0.70  thf('99', plain, (((r2_hidden @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('simplify', [status(thm)], ['68'])).
% 0.46/0.70  thf('100', plain,
% 0.46/0.70      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A)) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('clc', [status(thm)], ['98', '99'])).
% 0.46/0.70  thf('101', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '100'])).
% 0.46/0.70  thf('102', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('103', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.46/0.70      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.70  thf('104', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X5)
% 0.46/0.70          | ~ (v3_ordinal1 @ X6)
% 0.46/0.70          | (r1_tarski @ X5 @ X6)
% 0.46/0.70          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.70  thf('105', plain,
% 0.46/0.70      (((r1_tarski @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.70  thf('106', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('107', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('108', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.70      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.46/0.70  thf('109', plain,
% 0.46/0.70      (![X0 : $i, X2 : $i]:
% 0.46/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('110', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.70  thf('111', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('112', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.46/0.70  thf('113', plain,
% 0.46/0.70      (![X26 : $i]:
% 0.46/0.70         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.70  thf('114', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X7)
% 0.46/0.70          | (r2_hidden @ X8 @ X7)
% 0.46/0.70          | ((X8) = (X7))
% 0.46/0.70          | (r2_hidden @ X7 @ X8)
% 0.46/0.70          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.70      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.46/0.70  thf('115', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((r1_tarski @ X1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ X1))),
% 0.46/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.70  thf('116', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.70          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.70  thf('117', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((r1_ordinal1 @ X0 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.70  thf('118', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X9 @ (k3_relat_1 @ (k2_wellord1 @ X10 @ X11)))
% 0.46/0.70          | (r2_hidden @ X9 @ (k3_relat_1 @ X10))
% 0.46/0.70          | ~ (v1_relat_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.46/0.70  thf('119', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.46/0.70          | (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X1))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.70  thf('120', plain,
% 0.46/0.70      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('121', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('122', plain,
% 0.46/0.70      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('123', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.70          | (r2_hidden @ X2 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.46/0.70  thf('124', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X1)
% 0.46/0.70          | (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ((X1) = (X0))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ X1 @ X2)
% 0.46/0.70          | (r1_ordinal1 @ X2 @ X0)
% 0.46/0.70          | ~ (v3_ordinal1 @ X2)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['114', '123'])).
% 0.46/0.70  thf('125', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X2)
% 0.46/0.70          | (r1_ordinal1 @ X2 @ X0)
% 0.46/0.70          | (r2_hidden @ X1 @ X2)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | ((X1) = (X0))
% 0.46/0.70          | (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ~ (v3_ordinal1 @ X1))),
% 0.46/0.70      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.70  thf('126', plain,
% 0.46/0.70      (![X26 : $i]:
% 0.46/0.70         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.70  thf('127', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.70      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.46/0.70  thf('128', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.70          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.70  thf('129', plain,
% 0.46/0.70      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.70  thf('130', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.70             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ X1 @ X0)
% 0.46/0.70          | ((X0) = (X1))
% 0.46/0.70          | ~ (v3_ordinal1 @ X1)
% 0.46/0.70          | ~ (r2_hidden @ X0 @ X1)
% 0.46/0.70          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['37', '38', '42'])).
% 0.46/0.70  thf('131', plain,
% 0.46/0.70      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.70        | ((sk_A) = (sk_B))
% 0.46/0.70        | (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.70  thf('132', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.70  thf('133', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('134', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('135', plain,
% 0.46/0.70      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | ((sk_A) = (sk_B))
% 0.46/0.70        | (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.46/0.70  thf('136', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('137', plain,
% 0.46/0.70      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 0.46/0.70  thf('138', plain,
% 0.46/0.70      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.70        | (r2_hidden @ sk_B @ sk_A)
% 0.46/0.70        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['126', '137'])).
% 0.46/0.70  thf('139', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('140', plain,
% 0.46/0.70      (((r2_hidden @ sk_B @ sk_A) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['138', '139'])).
% 0.46/0.70  thf('141', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ sk_B)
% 0.46/0.70          | ((sk_B) = (sk_A))
% 0.46/0.70          | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70          | (r2_hidden @ sk_B @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['125', '140'])).
% 0.46/0.70  thf('142', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('143', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('144', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((sk_B) = (sk_A))
% 0.46/0.70          | (r2_hidden @ sk_B @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.46/0.70  thf('145', plain, (((sk_A) != (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('146', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r2_hidden @ sk_B @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.70          | ~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.46/0.70  thf('147', plain,
% 0.46/0.70      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.70  thf('148', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X9 @ (k3_relat_1 @ (k2_wellord1 @ X10 @ X11)))
% 0.46/0.70          | (r2_hidden @ X9 @ (k3_relat_1 @ X10))
% 0.46/0.70          | ~ (v1_relat_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.46/0.70  thf('149', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_A)))
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70          | (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_B))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['147', '148'])).
% 0.46/0.70  thf('150', plain,
% 0.46/0.70      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('151', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('152', plain,
% 0.46/0.70      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('153', plain,
% 0.46/0.70      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.46/0.70  thf('154', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X0)
% 0.46/0.70          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.70          | (r2_hidden @ sk_B @ X0)
% 0.46/0.70          | (r2_hidden @ sk_B @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['146', '153'])).
% 0.46/0.70  thf('155', plain,
% 0.46/0.70      (((r2_hidden @ sk_B @ sk_B)
% 0.46/0.70        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('eq_fact', [status(thm)], ['154'])).
% 0.46/0.70  thf('156', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('157', plain,
% 0.46/0.70      (((r2_hidden @ sk_B @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['155', '156'])).
% 0.46/0.70  thf('158', plain,
% 0.46/0.70      (![X24 : $i, X25 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X24)
% 0.46/0.70          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.70          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.70          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.70  thf('159', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.70        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_B))
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.70  thf('160', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('161', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('162', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.46/0.70  thf('163', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         (~ (v2_wellord1 @ X17)
% 0.46/0.70          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.70               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.70          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.70  thf('164', plain,
% 0.46/0.70      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.46/0.70           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_B))
% 0.46/0.70        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['162', '163'])).
% 0.46/0.70  thf('165', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.70  thf('166', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('167', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.70  thf('168', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X14)
% 0.46/0.70          | ~ (r4_wellord1 @ X15 @ X14)
% 0.46/0.70          | ~ (r4_wellord1 @ X14 @ X16)
% 0.46/0.70          | (r4_wellord1 @ X15 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.46/0.70  thf('169', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.46/0.70          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['167', '168'])).
% 0.46/0.70  thf('170', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('171', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('172', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0)
% 0.46/0.70          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.46/0.70          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170', '171'])).
% 0.46/0.70  thf('173', plain,
% 0.46/0.70      (((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))
% 0.46/0.70        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['166', '172'])).
% 0.46/0.70  thf('174', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('175', plain,
% 0.46/0.70      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['173', '174'])).
% 0.46/0.70  thf('176', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.70  thf('177', plain,
% 0.46/0.70      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('178', plain,
% 0.46/0.70      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.70        | ~ (r2_hidden @ sk_B @ sk_B)
% 0.46/0.70        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['164', '165', '175', '176', '177'])).
% 0.46/0.70  thf('179', plain,
% 0.46/0.70      (((r2_hidden @ sk_B @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['155', '156'])).
% 0.46/0.70  thf('180', plain,
% 0.46/0.70      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['178', '179'])).
% 0.46/0.70  thf('181', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['113', '180'])).
% 0.46/0.70  thf('182', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('183', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.46/0.70      inference('demod', [status(thm)], ['181', '182'])).
% 0.46/0.70  thf('184', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         (~ (v3_ordinal1 @ X5)
% 0.46/0.70          | ~ (v3_ordinal1 @ X6)
% 0.46/0.70          | (r1_tarski @ X5 @ X6)
% 0.46/0.70          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.70  thf('185', plain,
% 0.46/0.70      (((r1_tarski @ sk_B @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.70        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['183', '184'])).
% 0.46/0.70  thf('186', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('187', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('188', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.70      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.46/0.70  thf('189', plain, ($false), inference('demod', [status(thm)], ['112', '188'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.56/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
