%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gJdTl4OOVQ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 459 expanded)
%              Number of leaves         :   30 ( 145 expanded)
%              Depth                    :   34
%              Number of atoms          :  916 (4526 expanded)
%              Number of equality atoms :   49 ( 261 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

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

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ( r1_ordinal1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_xboole_0 @ X12 @ X11 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('27',plain,(
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

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('31',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('40',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','40'])).

thf('42',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('51',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_xboole_0 @ X12 @ X11 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('56',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('59',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('63',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('68',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('70',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('71',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('72',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('75',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('77',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('82',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('83',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','77','83'])).

thf('85',plain,(
    ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gJdTl4OOVQ
% 0.15/0.37  % Computer   : n019.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:58:53 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 191 iterations in 0.138s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.40/0.62  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.40/0.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.40/0.62  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.40/0.62  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.40/0.62  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.40/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.62  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.40/0.62  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.40/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.40/0.62  thf(t7_wellord2, axiom,
% 0.40/0.62    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X26 : $i]:
% 0.40/0.62         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.40/0.62  thf(connectedness_r1_ordinal1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.40/0.62       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X4 : $i, X5 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X4)
% 0.40/0.62          | ~ (v3_ordinal1 @ X5)
% 0.40/0.62          | (r1_ordinal1 @ X4 @ X5)
% 0.40/0.62          | (r1_ordinal1 @ X5 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.40/0.62  thf(redefinition_r1_ordinal1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.40/0.62       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X9)
% 0.40/0.62          | ~ (v3_ordinal1 @ X10)
% 0.40/0.62          | (r1_tarski @ X9 @ X10)
% 0.40/0.62          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_ordinal1 @ X0 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | (r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | (r1_ordinal1 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.62  thf(d8_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.40/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X0 : $i, X2 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_ordinal1 @ X0 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X9 : $i, X10 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X9)
% 0.40/0.62          | ~ (v3_ordinal1 @ X10)
% 0.40/0.62          | (r1_tarski @ X9 @ X10)
% 0.40/0.62          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X1)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | (r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X0 : $i, X2 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X1)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.62  thf(t21_ordinal1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_ordinal1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.62           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X11)
% 0.40/0.62          | (r2_hidden @ X12 @ X11)
% 0.40/0.62          | ~ (r2_xboole_0 @ X12 @ X11)
% 0.40/0.62          | ~ (v1_ordinal1 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X1)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v1_ordinal1 @ X1)
% 0.40/0.62          | (r2_hidden @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_hidden @ X1 @ X0)
% 0.40/0.62          | ~ (v1_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X26 : $i]:
% 0.40/0.62         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.40/0.62  thf(t11_wellord2, conjecture,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.62           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.40/0.62             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i]:
% 0.40/0.62        ( ( v3_ordinal1 @ A ) =>
% 0.40/0.62          ( ![B:$i]:
% 0.40/0.62            ( ( v3_ordinal1 @ B ) =>
% 0.40/0.62              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.40/0.62                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.62  thf(t8_wellord2, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.40/0.62       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X27 : $i, X28 : $i]:
% 0.40/0.62         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.40/0.62          | ~ (r1_tarski @ X27 @ X28))),
% 0.40/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X1)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_hidden @ X1 @ X0)
% 0.40/0.62          | ~ (v1_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.62  thf(t10_wellord2, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.62           ( ( r2_hidden @ A @ B ) =>
% 0.40/0.62             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X24)
% 0.40/0.62          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.40/0.62          | ~ (r2_hidden @ X25 @ X24)
% 0.40/0.62          | ~ (v3_ordinal1 @ X25))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_xboole_0 @ X0 @ X1)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v1_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.40/0.62          | ~ (v1_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ((X0) = (X1))
% 0.40/0.62          | (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.62  thf(t57_wellord1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ( v2_wellord1 @ A ) =>
% 0.40/0.62         ( ![B:$i]:
% 0.40/0.62           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.40/0.62                ( r4_wellord1 @
% 0.40/0.62                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i]:
% 0.40/0.62         (~ (v2_wellord1 @ X17)
% 0.40/0.62          | ~ (r4_wellord1 @ X17 @ 
% 0.40/0.62               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.40/0.62          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.40/0.62          | ~ (v1_relat_1 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.40/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v1_ordinal1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.40/0.62          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.40/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.62  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.40/0.62  thf('27', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.40/0.62  thf(d1_wellord2, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.40/0.62         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.40/0.62           ( ![C:$i,D:$i]:
% 0.40/0.62             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.40/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.40/0.62                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i]:
% 0.40/0.62         (((X20) != (k1_wellord2 @ X19))
% 0.40/0.62          | ((k3_relat_1 @ X20) = (X19))
% 0.40/0.62          | ~ (v1_relat_1 @ X20))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X19 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.40/0.62          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.62  thf('30', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.40/0.62  thf('31', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.40/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v1_ordinal1 @ X0)
% 0.40/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.40/0.62      inference('demod', [status(thm)], ['26', '27', '31'])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.40/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | ~ (v1_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['20', '32'])).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_ordinal1 @ X0)
% 0.40/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.40/0.62          | (r2_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ((X1) = (X0))
% 0.40/0.62          | ~ (v3_ordinal1 @ X1)
% 0.40/0.62          | ~ (v3_ordinal1 @ X0)
% 0.40/0.62          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((~ (v3_ordinal1 @ sk_B_1)
% 0.40/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.40/0.62        | ((sk_A) = (sk_B_1))
% 0.40/0.62        | (r2_xboole_0 @ sk_A @ sk_B_1)
% 0.40/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.40/0.62        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.40/0.62        | ~ (v1_ordinal1 @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['17', '34'])).
% 0.40/0.62  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('38', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(cc1_ordinal1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.40/0.62  thf('39', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.40/0.62  thf('40', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      ((((sk_A) = (sk_B_1))
% 0.40/0.62        | (r2_xboole_0 @ sk_A @ sk_B_1)
% 0.40/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.40/0.62        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['35', '36', '37', '40'])).
% 0.40/0.62  thf('42', plain, (((sk_A) != (sk_B_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (((r2_xboole_0 @ sk_A @ sk_B_1)
% 0.40/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.40/0.62        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.40/0.62        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.40/0.62        | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['16', '43'])).
% 0.40/0.62  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      ((~ (r2_hidden @ sk_B_1 @ sk_A) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.62  thf('47', plain,
% 0.40/0.62      (((r2_xboole_0 @ sk_A @ sk_B_1)
% 0.40/0.62        | ((sk_A) = (sk_B_1))
% 0.40/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.40/0.62        | ~ (v3_ordinal1 @ sk_B_1)
% 0.40/0.62        | ~ (v1_ordinal1 @ sk_B_1)
% 0.40/0.62        | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '46'])).
% 0.40/0.62  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('49', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('50', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (((r2_xboole_0 @ sk_A @ sk_B_1)
% 0.40/0.62        | ((sk_A) = (sk_B_1))
% 0.40/0.62        | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.40/0.62  thf('52', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.62  thf('53', plain, (((sk_A) != (sk_B_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('54', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X11)
% 0.40/0.62          | (r2_hidden @ X12 @ X11)
% 0.40/0.62          | ~ (r2_xboole_0 @ X12 @ X11)
% 0.40/0.62          | ~ (v1_ordinal1 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.40/0.62  thf('56', plain,
% 0.40/0.62      ((~ (v1_ordinal1 @ sk_A)
% 0.40/0.62        | (r2_hidden @ sk_A @ sk_B_1)
% 0.40/0.62        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.62  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('58', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.40/0.62  thf('59', plain, ((v1_ordinal1 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.62  thf('60', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('61', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]:
% 0.40/0.62         (~ (v3_ordinal1 @ X24)
% 0.40/0.62          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.40/0.62          | ~ (r2_hidden @ X25 @ X24)
% 0.40/0.62          | ~ (v3_ordinal1 @ X25))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.40/0.62  thf('63', plain,
% 0.40/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.40/0.62        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.40/0.62        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.62  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('65', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('66', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.40/0.62  thf('67', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i]:
% 0.40/0.62         (~ (v2_wellord1 @ X17)
% 0.40/0.62          | ~ (r4_wellord1 @ X17 @ 
% 0.40/0.62               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.40/0.62          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.40/0.62          | ~ (v1_relat_1 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.40/0.62  thf('68', plain,
% 0.40/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ 
% 0.40/0.62           (k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.40/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1))
% 0.40/0.62        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B_1)))
% 0.40/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.40/0.62  thf('69', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.40/0.62  thf('70', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('71', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.40/0.62  thf('72', plain,
% 0.40/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ 
% 0.40/0.62           (k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.40/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1)))),
% 0.40/0.62      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.40/0.62  thf('73', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.40/0.62  thf('74', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.62  thf('75', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.62  thf('76', plain,
% 0.40/0.62      (![X27 : $i, X28 : $i]:
% 0.40/0.62         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.40/0.62          | ~ (r1_tarski @ X27 @ X28))),
% 0.40/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.40/0.62  thf('77', plain,
% 0.40/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.40/0.62  thf('78', plain,
% 0.40/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t50_wellord1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v1_relat_1 @ B ) =>
% 0.40/0.62           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('79', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X15)
% 0.40/0.62          | (r4_wellord1 @ X15 @ X16)
% 0.40/0.62          | ~ (r4_wellord1 @ X16 @ X15)
% 0.40/0.62          | ~ (v1_relat_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.40/0.62  thf('80', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.40/0.62        | (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))
% 0.40/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['78', '79'])).
% 0.40/0.62  thf('81', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.40/0.62  thf('82', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.40/0.62  thf('83', plain,
% 0.40/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.40/0.62  thf('84', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))),
% 0.40/0.62      inference('demod', [status(thm)], ['72', '77', '83'])).
% 0.40/0.62  thf('85', plain, (~ (v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '84'])).
% 0.40/0.62  thf('86', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('87', plain, ($false), inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
