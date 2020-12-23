%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wY6R97XCU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 385 expanded)
%              Number of leaves         :   27 ( 123 expanded)
%              Depth                    :   32
%              Number of atoms          :  912 (3891 expanded)
%              Number of equality atoms :   52 ( 249 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X29 ) )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r2_hidden @ X15 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k1_ordinal1 @ X16 ) )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X29: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X29 ) )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
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

thf('8',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k1_ordinal1 @ X16 ) )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X31 ) @ X30 )
        = ( k1_wellord2 @ X30 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( X28
        = ( k1_wellord1 @ ( k1_wellord2 @ X27 ) @ X28 ) )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_wellord1 @ X20 )
      | ~ ( r4_wellord1 @ X20 @ ( k2_wellord1 @ X20 @ ( k1_wellord1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('26',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
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

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
       != ( k1_wellord2 @ X22 ) )
      | ( ( k3_relat_1 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('28',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X22 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
        = X22 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A = sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_A = sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X17 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('51',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('56',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( X28
        = ( k1_wellord1 @ ( k1_wellord2 @ X27 ) @ X28 ) )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('60',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_wellord1 @ X20 )
      | ~ ( r4_wellord1 @ X20 @ ( k2_wellord1 @ X20 @ ( k1_wellord1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('65',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('68',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('69',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X31 ) @ X30 )
        = ( k1_wellord2 @ X30 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('77',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r4_wellord1 @ X18 @ X19 )
      | ~ ( r4_wellord1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('82',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('83',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','77','83'])).

thf('85',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wY6R97XCU
% 0.13/0.36  % Computer   : n009.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:39:56 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 171 iterations in 0.120s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.59  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.22/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.59  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.59  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.22/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.59  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.59  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.22/0.59  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.22/0.59  thf(t7_wellord2, axiom,
% 0.22/0.59    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      (![X29 : $i]:
% 0.22/0.59         ((v2_wellord1 @ (k1_wellord2 @ X29)) | ~ (v3_ordinal1 @ X29))),
% 0.22/0.59      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.22/0.59  thf(t24_ordinal1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.59           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.22/0.59                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (![X14 : $i, X15 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X14)
% 0.22/0.59          | (r2_hidden @ X15 @ X14)
% 0.22/0.59          | ((X15) = (X14))
% 0.22/0.59          | (r2_hidden @ X14 @ X15)
% 0.22/0.59          | ~ (v3_ordinal1 @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.22/0.59  thf(t13_ordinal1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.59       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r2_hidden @ X0 @ X1)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.59  thf(t34_ordinal1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.59           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.59             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (![X16 : $i, X17 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X16)
% 0.22/0.59          | ~ (r2_hidden @ X17 @ (k1_ordinal1 @ X16))
% 0.22/0.59          | (r1_ordinal1 @ X17 @ X16)
% 0.22/0.59          | ~ (v3_ordinal1 @ X17))),
% 0.22/0.59      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | (r2_hidden @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r2_hidden @ X0 @ X1)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (![X29 : $i]:
% 0.22/0.59         ((v2_wellord1 @ (k1_wellord2 @ X29)) | ~ (v3_ordinal1 @ X29))),
% 0.22/0.59      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.22/0.59  thf(t11_wellord2, conjecture,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.59           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.22/0.59             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i]:
% 0.22/0.59        ( ( v3_ordinal1 @ A ) =>
% 0.22/0.59          ( ![B:$i]:
% 0.22/0.59            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.59              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.22/0.59                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r2_hidden @ X0 @ X1)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      (![X16 : $i, X17 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X16)
% 0.22/0.59          | ~ (r2_hidden @ X17 @ (k1_ordinal1 @ X16))
% 0.22/0.59          | (r1_ordinal1 @ X17 @ X16)
% 0.22/0.59          | ~ (v3_ordinal1 @ X17))),
% 0.22/0.59      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.59  thf('13', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | (r1_ordinal1 @ X0 @ X1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.22/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.59  thf('15', plain,
% 0.22/0.59      (![X7 : $i, X8 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X7)
% 0.22/0.59          | ~ (v3_ordinal1 @ X8)
% 0.22/0.59          | (r1_tarski @ X7 @ X8)
% 0.22/0.59          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.22/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.59  thf('16', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r1_tarski @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_tarski @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | (r1_ordinal1 @ X0 @ X1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.59  thf(t8_wellord2, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.59       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.22/0.59  thf('18', plain,
% 0.22/0.59      (![X30 : $i, X31 : $i]:
% 0.22/0.59         (((k2_wellord1 @ (k1_wellord2 @ X31) @ X30) = (k1_wellord2 @ X30))
% 0.22/0.59          | ~ (r1_tarski @ X30 @ X31))),
% 0.22/0.59      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r2_hidden @ X0 @ X1)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.59  thf(t10_wellord2, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.59           ( ( r2_hidden @ A @ B ) =>
% 0.22/0.59             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (![X27 : $i, X28 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X27)
% 0.22/0.59          | ((X28) = (k1_wellord1 @ (k1_wellord2 @ X27) @ X28))
% 0.22/0.59          | ~ (r2_hidden @ X28 @ X27)
% 0.22/0.59          | ~ (v3_ordinal1 @ X28))),
% 0.22/0.59      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.22/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X0) = (X1))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.59  thf(t57_wellord1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v1_relat_1 @ A ) =>
% 0.22/0.59       ( ( v2_wellord1 @ A ) =>
% 0.22/0.59         ( ![B:$i]:
% 0.22/0.59           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.22/0.59                ( r4_wellord1 @
% 0.22/0.59                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf('24', plain,
% 0.22/0.59      (![X20 : $i, X21 : $i]:
% 0.22/0.59         (~ (v2_wellord1 @ X20)
% 0.22/0.59          | ~ (r4_wellord1 @ X20 @ 
% 0.22/0.59               (k2_wellord1 @ X20 @ (k1_wellord1 @ X20 @ X21)))
% 0.22/0.59          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.22/0.59          | ~ (v1_relat_1 @ X20))),
% 0.22/0.59      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.22/0.59             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.22/0.59          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.22/0.59          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.59  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.22/0.59  thf('26', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.59  thf(d1_wellord2, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( v1_relat_1 @ B ) =>
% 0.22/0.59       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.22/0.59         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.59           ( ![C:$i,D:$i]:
% 0.22/0.59             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.22/0.59               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.22/0.59                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (![X22 : $i, X23 : $i]:
% 0.22/0.59         (((X23) != (k1_wellord2 @ X22))
% 0.22/0.59          | ((k3_relat_1 @ X23) = (X22))
% 0.22/0.59          | ~ (v1_relat_1 @ X23))),
% 0.22/0.59      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      (![X22 : $i]:
% 0.22/0.59         (~ (v1_relat_1 @ (k1_wellord2 @ X22))
% 0.22/0.59          | ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22)))),
% 0.22/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.59  thf('29', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.59  thf('30', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.22/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.22/0.59             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X0)
% 0.22/0.59          | ((X1) = (X0))
% 0.22/0.59          | ~ (v3_ordinal1 @ X1)
% 0.22/0.59          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.59          | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.60          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.22/0.60      inference('demod', [status(thm)], ['25', '26', '30'])).
% 0.22/0.60  thf('32', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.22/0.60          | ~ (v3_ordinal1 @ X0)
% 0.22/0.60          | ((X1) = (X0))
% 0.22/0.60          | ~ (v3_ordinal1 @ X1)
% 0.22/0.60          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.60          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.22/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.60          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.60          | ~ (v3_ordinal1 @ X1)
% 0.22/0.60          | ((X1) = (X0))
% 0.22/0.60          | ~ (v3_ordinal1 @ X0))),
% 0.22/0.60      inference('sup-', [status(thm)], ['19', '31'])).
% 0.22/0.60  thf('33', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.60          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.22/0.60          | (r1_ordinal1 @ X1 @ X0)
% 0.22/0.60          | ~ (v3_ordinal1 @ X1)
% 0.22/0.60          | ((X1) = (X0))
% 0.22/0.60          | ~ (v3_ordinal1 @ X0)
% 0.22/0.60          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.60  thf('34', plain,
% 0.22/0.60      ((~ (v3_ordinal1 @ sk_B)
% 0.22/0.60        | ((sk_A) = (sk_B))
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.60        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.60        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.60      inference('sup-', [status(thm)], ['8', '33'])).
% 0.22/0.60  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('37', plain,
% 0.22/0.60      ((((sk_A) = (sk_B))
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.60        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.60        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.60      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.60  thf('38', plain, (((sk_A) != (sk_B))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('39', plain,
% 0.22/0.60      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.60        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.22/0.60        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.60  thf('40', plain,
% 0.22/0.60      ((~ (v3_ordinal1 @ sk_A)
% 0.22/0.60        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.60      inference('sup-', [status(thm)], ['7', '39'])).
% 0.22/0.60  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('42', plain,
% 0.22/0.60      ((~ (r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.60  thf('43', plain,
% 0.22/0.60      ((~ (v3_ordinal1 @ sk_B)
% 0.22/0.60        | ((sk_A) = (sk_B))
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.60      inference('sup-', [status(thm)], ['6', '42'])).
% 0.22/0.60  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('46', plain,
% 0.22/0.60      ((((sk_A) = (sk_B))
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.60        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.60      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.60  thf('47', plain, (((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.60  thf('48', plain, (((sk_A) != (sk_B))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('49', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.22/0.60  thf('50', plain,
% 0.22/0.60      (![X16 : $i, X17 : $i]:
% 0.22/0.60         (~ (v3_ordinal1 @ X16)
% 0.22/0.60          | ~ (r1_ordinal1 @ X17 @ X16)
% 0.22/0.60          | (r2_hidden @ X17 @ (k1_ordinal1 @ X16))
% 0.22/0.60          | ~ (v3_ordinal1 @ X17))),
% 0.22/0.60      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.22/0.60  thf('51', plain,
% 0.22/0.60      ((~ (v3_ordinal1 @ sk_A)
% 0.22/0.60        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.60  thf('52', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('54', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.22/0.60      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.22/0.60  thf('55', plain,
% 0.22/0.60      (![X9 : $i, X10 : $i]:
% 0.22/0.60         (((X10) = (X9))
% 0.22/0.60          | (r2_hidden @ X10 @ X9)
% 0.22/0.60          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.22/0.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.60  thf('56', plain, (((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.60  thf('57', plain, (((sk_A) != (sk_B))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('58', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.60  thf('59', plain,
% 0.22/0.60      (![X27 : $i, X28 : $i]:
% 0.22/0.60         (~ (v3_ordinal1 @ X27)
% 0.22/0.60          | ((X28) = (k1_wellord1 @ (k1_wellord2 @ X27) @ X28))
% 0.22/0.60          | ~ (r2_hidden @ X28 @ X27)
% 0.22/0.60          | ~ (v3_ordinal1 @ X28))),
% 0.22/0.60      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.22/0.60  thf('60', plain,
% 0.22/0.60      ((~ (v3_ordinal1 @ sk_A)
% 0.22/0.60        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_B))),
% 0.22/0.60      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.60  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('63', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.22/0.60      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.22/0.60  thf('64', plain,
% 0.22/0.60      (![X20 : $i, X21 : $i]:
% 0.22/0.60         (~ (v2_wellord1 @ X20)
% 0.22/0.60          | ~ (r4_wellord1 @ X20 @ 
% 0.22/0.60               (k2_wellord1 @ X20 @ (k1_wellord1 @ X20 @ X21)))
% 0.22/0.60          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.22/0.60          | ~ (v1_relat_1 @ X20))),
% 0.22/0.60      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.22/0.60  thf('65', plain,
% 0.22/0.60      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.22/0.60           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.22/0.60        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.22/0.60        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.22/0.60        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.60  thf('66', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.22/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.60  thf('67', plain, (![X22 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X22)) = (X22))),
% 0.22/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.60  thf('68', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.60  thf('69', plain,
% 0.22/0.60      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.22/0.60           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.22/0.60        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.22/0.60      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.22/0.60  thf('70', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.22/0.60      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.22/0.60  thf('71', plain,
% 0.22/0.60      (![X7 : $i, X8 : $i]:
% 0.22/0.60         (~ (v3_ordinal1 @ X7)
% 0.22/0.60          | ~ (v3_ordinal1 @ X8)
% 0.22/0.60          | (r1_tarski @ X7 @ X8)
% 0.22/0.60          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.22/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.60  thf('72', plain,
% 0.22/0.60      (((r1_tarski @ sk_A @ sk_B)
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.60        | ~ (v3_ordinal1 @ sk_A))),
% 0.22/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.60  thf('73', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('75', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.60      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.22/0.60  thf('76', plain,
% 0.22/0.60      (![X30 : $i, X31 : $i]:
% 0.22/0.60         (((k2_wellord1 @ (k1_wellord2 @ X31) @ X30) = (k1_wellord2 @ X30))
% 0.22/0.60          | ~ (r1_tarski @ X30 @ X31))),
% 0.22/0.60      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.22/0.60  thf('77', plain,
% 0.22/0.60      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.22/0.60      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.60  thf('78', plain,
% 0.22/0.60      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf(t50_wellord1, axiom,
% 0.22/0.60    (![A:$i]:
% 0.22/0.60     ( ( v1_relat_1 @ A ) =>
% 0.22/0.60       ( ![B:$i]:
% 0.22/0.60         ( ( v1_relat_1 @ B ) =>
% 0.22/0.60           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.22/0.60  thf('79', plain,
% 0.22/0.60      (![X18 : $i, X19 : $i]:
% 0.22/0.60         (~ (v1_relat_1 @ X18)
% 0.22/0.60          | (r4_wellord1 @ X18 @ X19)
% 0.22/0.60          | ~ (r4_wellord1 @ X19 @ X18)
% 0.22/0.60          | ~ (v1_relat_1 @ X19))),
% 0.22/0.60      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.22/0.60  thf('80', plain,
% 0.22/0.60      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.22/0.60        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.22/0.60        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.22/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.60  thf('81', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.22/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.60  thf('82', plain, (![X26 : $i]: (v1_relat_1 @ (k1_wellord2 @ X26))),
% 0.22/0.60      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.60  thf('83', plain,
% 0.22/0.60      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.22/0.60      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.22/0.60  thf('84', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.22/0.60      inference('demod', [status(thm)], ['69', '77', '83'])).
% 0.22/0.60  thf('85', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('sup-', [status(thm)], ['0', '84'])).
% 0.22/0.60  thf('86', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.60  thf('87', plain, ($false), inference('demod', [status(thm)], ['85', '86'])).
% 0.22/0.60  
% 0.22/0.60  % SZS output end Refutation
% 0.22/0.60  
% 0.22/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
