%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u707J2Te1m

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 639 expanded)
%              Number of leaves         :   28 ( 196 expanded)
%              Depth                    :   31
%              Number of atoms          :  951 (5914 expanded)
%              Number of equality atoms :   33 ( 274 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
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

thf('1',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X11 @ X10 )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_ordinal1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_B @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( sk_A = sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X27 ) @ X26 )
        = ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
      = ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X11 @ X10 )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( X24
        = ( k1_wellord1 @ ( k1_wellord2 @ X23 ) @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ ( k2_wellord1 @ X16 @ ( k1_wellord1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
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

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
       != ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ X19 )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('43',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','45'])).

thf('47',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('55',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k1_ordinal1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('60',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','62'])).

thf('64',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('68',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('77',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('78',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X27 ) @ X26 )
        = ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('79',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','45'])).

thf('81',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r4_wellord1 @ X14 @ X15 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('86',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('87',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('90',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k1_ordinal1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('95',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','87','97','98','99'])).

thf('101',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','100'])).

thf('102',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('105',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['75','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u707J2Te1m
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 116 iterations in 0.076s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.22/0.54  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.54  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.54  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.22/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.54  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.22/0.54  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.54  thf(t7_wellord2, axiom,
% 0.22/0.54    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X25 : $i]:
% 0.22/0.54         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.22/0.54  thf(t11_wellord2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.54           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.22/0.54             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( v3_ordinal1 @ A ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.54              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.22/0.54                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.22/0.54  thf('1', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t26_ordinal1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.54           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X10)
% 0.22/0.54          | (r1_ordinal1 @ X11 @ X10)
% 0.22/0.54          | (r2_hidden @ X10 @ X11)
% 0.22/0.54          | ~ (v3_ordinal1 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.54  thf(t13_ordinal1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.54       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         ((r2_hidden @ X6 @ (k1_ordinal1 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1)
% 0.22/0.54          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf(t34_ordinal1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.54           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.54             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X12)
% 0.22/0.54          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.22/0.54          | (r1_ordinal1 @ X13 @ X12)
% 0.22/0.54          | ~ (v3_ordinal1 @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X1)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1)
% 0.22/0.54          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.54  thf(redefinition_r1_ordinal1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.22/0.54       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X3)
% 0.22/0.54          | ~ (v3_ordinal1 @ X4)
% 0.22/0.54          | (r1_tarski @ X3 @ X4)
% 0.22/0.54          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X1)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_tarski @ X1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ sk_B @ X0)
% 0.22/0.54          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '10'])).
% 0.22/0.54  thf('12', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ sk_A @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X3)
% 0.22/0.54          | ~ (v3_ordinal1 @ X4)
% 0.22/0.54          | (r1_tarski @ X3 @ X4)
% 0.22/0.54          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_ordinal1 @ sk_A @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_tarski @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_ordinal1 @ sk_A @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_tarski @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ sk_A @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_ordinal1 @ sk_A @ X0)
% 0.22/0.54          | ~ (v3_ordinal1 @ X0)
% 0.22/0.54          | ~ (r1_tarski @ sk_A @ X0)
% 0.22/0.54          | ((sk_A) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.22/0.54        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.54        | ((sk_A) = (sk_B))
% 0.22/0.54        | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.54        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '21'])).
% 0.22/0.54  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.22/0.54        | ((sk_A) = (sk_B))
% 0.22/0.54        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.54  thf('26', plain, (((sk_A) != (sk_B))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X3)
% 0.22/0.54          | ~ (v3_ordinal1 @ X4)
% 0.22/0.54          | (r1_tarski @ X3 @ X4)
% 0.22/0.54          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.54        | (r1_tarski @ sk_B @ sk_A)
% 0.22/0.54        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.54        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('32', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.54  thf(t8_wellord2, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.54       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i]:
% 0.22/0.54         (((k2_wellord1 @ (k1_wellord2 @ X27) @ X26) = (k1_wellord2 @ X26))
% 0.22/0.54          | ~ (r1_tarski @ X26 @ X27))),
% 0.22/0.54      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.54        | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X10)
% 0.22/0.54          | (r1_ordinal1 @ X11 @ X10)
% 0.22/0.54          | (r2_hidden @ X10 @ X11)
% 0.22/0.54          | ~ (v3_ordinal1 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.54  thf(t10_wellord2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.54           ( ( r2_hidden @ A @ B ) =>
% 0.22/0.54             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X23)
% 0.22/0.54          | ((X24) = (k1_wellord1 @ (k1_wellord2 @ X23) @ X24))
% 0.22/0.54          | ~ (r2_hidden @ X24 @ X23)
% 0.22/0.54          | ~ (v3_ordinal1 @ X24))),
% 0.22/0.54      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_ordinal1 @ X0)
% 0.22/0.54          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1)
% 0.22/0.54          | ~ (v3_ordinal1 @ X1)
% 0.22/0.54          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.22/0.54          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.22/0.55          | ~ (v3_ordinal1 @ X1)
% 0.22/0.55          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.55  thf(t57_wellord1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ( v2_wellord1 @ A ) =>
% 0.22/0.55         ( ![B:$i]:
% 0.22/0.55           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.22/0.55                ( r4_wellord1 @
% 0.22/0.55                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         (~ (v2_wellord1 @ X16)
% 0.22/0.55          | ~ (r4_wellord1 @ X16 @ 
% 0.22/0.55               (k2_wellord1 @ X16 @ (k1_wellord1 @ X16 @ X17)))
% 0.22/0.55          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 0.22/0.55          | ~ (v1_relat_1 @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.22/0.55             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.22/0.55          | ~ (v3_ordinal1 @ X1)
% 0.22/0.55          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.55          | ~ (v3_ordinal1 @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.22/0.55          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.22/0.55  thf('41', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.55  thf(d1_wellord2, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ B ) =>
% 0.22/0.55       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.22/0.55         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.55           ( ![C:$i,D:$i]:
% 0.22/0.55             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.22/0.55               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.22/0.55                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i]:
% 0.22/0.55         (((X19) != (k1_wellord2 @ X18))
% 0.22/0.55          | ((k3_relat_1 @ X19) = (X18))
% 0.22/0.55          | ~ (v1_relat_1 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X18 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X18))
% 0.22/0.55          | ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.55  thf('44', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.55  thf('45', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.22/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.22/0.55             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.22/0.55          | ~ (v3_ordinal1 @ X1)
% 0.22/0.55          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.55          | ~ (v3_ordinal1 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.55          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.22/0.55      inference('demod', [status(thm)], ['40', '41', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.22/0.55        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.55        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['34', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.22/0.55        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.22/0.55        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (v3_ordinal1 @ X12)
% 0.22/0.55          | ~ (r1_ordinal1 @ X13 @ X12)
% 0.22/0.55          | (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.22/0.55          | ~ (v3_ordinal1 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.55        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.55  thf('56', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]:
% 0.22/0.55         (((X6) = (X5))
% 0.22/0.55          | (r2_hidden @ X6 @ X5)
% 0.22/0.55          | ~ (r2_hidden @ X6 @ (k1_ordinal1 @ X5)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.55        | (r2_hidden @ sk_B @ sk_A)
% 0.22/0.55        | ((sk_B) = (sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, (((sk_A) != (sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (((r1_ordinal1 @ sk_A @ sk_B) | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '62'])).
% 0.22/0.55  thf('64', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '63'])).
% 0.22/0.55  thf('65', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('66', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (v3_ordinal1 @ X3)
% 0.22/0.55          | ~ (v3_ordinal1 @ X4)
% 0.22/0.55          | (r1_tarski @ X3 @ X4)
% 0.22/0.55          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (((r1_tarski @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.55  thf('69', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('71', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      (![X0 : $i, X2 : $i]:
% 0.22/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('73', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.55  thf('74', plain, (((sk_A) != (sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('75', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (![X25 : $i]:
% 0.22/0.55         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.22/0.55  thf('77', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (![X26 : $i, X27 : $i]:
% 0.22/0.55         (((k2_wellord1 @ (k1_wellord2 @ X27) @ X26) = (k1_wellord2 @ X26))
% 0.22/0.55          | ~ (r1_tarski @ X26 @ X27))),
% 0.22/0.55      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.22/0.55             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.22/0.55          | ~ (v3_ordinal1 @ X1)
% 0.22/0.55          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.55          | ~ (v3_ordinal1 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.55          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.22/0.55      inference('demod', [status(thm)], ['40', '41', '45'])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.22/0.55        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.55        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t50_wellord1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( v1_relat_1 @ B ) =>
% 0.22/0.55           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (![X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X14)
% 0.22/0.55          | (r4_wellord1 @ X14 @ X15)
% 0.22/0.55          | ~ (r4_wellord1 @ X15 @ X14)
% 0.22/0.55          | ~ (v1_relat_1 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.22/0.55  thf('84', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.22/0.55        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.55  thf('85', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.55  thf('86', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.22/0.55  thf('88', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (v3_ordinal1 @ X12)
% 0.22/0.55          | ~ (r1_ordinal1 @ X13 @ X12)
% 0.22/0.55          | (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.22/0.55          | ~ (v3_ordinal1 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      ((~ (v3_ordinal1 @ sk_A)
% 0.22/0.55        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.55  thf('91', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('92', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('93', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]:
% 0.22/0.55         (((X6) = (X5))
% 0.22/0.55          | (r2_hidden @ X6 @ X5)
% 0.22/0.55          | ~ (r2_hidden @ X6 @ (k1_ordinal1 @ X5)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.55  thf('95', plain, (((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.55  thf('96', plain, (((sk_A) != (sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('97', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.22/0.55  thf('98', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('99', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('100', plain,
% 0.22/0.55      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['81', '87', '97', '98', '99'])).
% 0.22/0.55  thf('101', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['76', '100'])).
% 0.22/0.55  thf('102', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('103', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['101', '102'])).
% 0.22/0.55  thf('104', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (v3_ordinal1 @ X3)
% 0.22/0.55          | ~ (v3_ordinal1 @ X4)
% 0.22/0.55          | (r1_tarski @ X3 @ X4)
% 0.22/0.55          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.55  thf('105', plain,
% 0.22/0.55      (((r1_tarski @ sk_B @ sk_A)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.55        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.55  thf('106', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('107', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('108', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.22/0.55  thf('109', plain, ($false), inference('demod', [status(thm)], ['75', '108'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
