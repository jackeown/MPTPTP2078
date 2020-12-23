%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8JuqF6F5N

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:39 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 157 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  658 (1204 expanded)
%              Number of equality atoms :   86 ( 168 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ X21 @ X18 ) @ ( sk_D @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C_3 @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X27 @ X28 ) )
        = X28 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X27 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X27 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X27 @ X28 ) )
        = ( k1_tarski @ X27 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('22',plain,(
    ! [X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('37',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('41',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( sk_B @ X25 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( sk_B @ X25 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('48',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['30','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','48'])).

thf('58',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8JuqF6F5N
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:42:49 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 104 iterations in 0.051s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.35/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(d4_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]:
% 0.35/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.35/0.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X18 : $i, X21 : $i]:
% 0.35/0.54         (((X21) = (k1_relat_1 @ X18))
% 0.35/0.54          | (r2_hidden @ 
% 0.35/0.54             (k4_tarski @ (sk_C_3 @ X21 @ X18) @ (sk_D @ X21 @ X18)) @ X18)
% 0.35/0.54          | (r2_hidden @ (sk_C_3 @ X21 @ X18) @ X21))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.35/0.54  thf(t2_boole, axiom,
% 0.35/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.54  thf(t4_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.35/0.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.54  thf('4', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.35/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.54  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.54          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '5'])).
% 0.35/0.54  thf(t60_relat_1, axiom,
% 0.35/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.54          | ((X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf(t15_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ?[C:$i]:
% 0.35/0.54           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.35/0.54             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.35/0.54             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X27 : $i, X28 : $i]:
% 0.35/0.54         (((k1_relat_1 @ (sk_C_4 @ X27 @ X28)) = (X28))
% 0.35/0.54          | ((X28) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X27 : $i, X28 : $i]:
% 0.35/0.54         ((v1_relat_1 @ (sk_C_4 @ X27 @ X28)) | ((X28) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X27 : $i, X28 : $i]:
% 0.35/0.54         ((v1_funct_1 @ (sk_C_4 @ X27 @ X28)) | ((X28) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.35/0.54  thf(d3_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X1 : $i, X3 : $i]:
% 0.35/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X1 : $i, X3 : $i]:
% 0.35/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X14 @ X13)
% 0.35/0.54          | ((X14) = (X11))
% 0.35/0.54          | ((X13) != (k1_tarski @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X11 : $i, X14 : $i]:
% 0.35/0.54         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.54          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '15'])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X1 : $i, X3 : $i]:
% 0.35/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.35/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ X1)
% 0.35/0.54          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '19'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X27 : $i, X28 : $i]:
% 0.35/0.54         (((k2_relat_1 @ (sk_C_4 @ X27 @ X28)) = (k1_tarski @ X27))
% 0.35/0.54          | ((X28) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.35/0.54  thf(t18_funct_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54          ( ![C:$i]:
% 0.35/0.54            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.54              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.35/0.54                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54             ( ![C:$i]:
% 0.35/0.54               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.54                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.35/0.54                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X29 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k2_relat_1 @ X29) @ sk_A)
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ X29))
% 0.35/0.54          | ~ (v1_funct_1 @ X29)
% 0.35/0.54          | ~ (v1_relat_1 @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.35/0.54          | ((X1) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.35/0.54          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ sk_A @ X0)
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.35/0.54          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.35/0.54          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.35/0.54          | ((X1) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((X0) = (k1_xboole_0))
% 0.35/0.54          | ((X0) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.35/0.54          | (r1_tarski @ sk_A @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ sk_A @ X1)
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.35/0.54          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.35/0.54          | ((X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((X0) = (k1_xboole_0))
% 0.35/0.54          | ((X0) = (k1_xboole_0))
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.35/0.54          | (r1_tarski @ sk_A @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ sk_A @ X1)
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.35/0.54          | ((X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((sk_B_1) != (X0))
% 0.35/0.54          | ((X0) = (k1_xboole_0))
% 0.35/0.54          | ((X0) = (k1_xboole_0))
% 0.35/0.54          | (r1_tarski @ sk_A @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.54  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X29 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k2_relat_1 @ X29) @ sk_A)
% 0.35/0.54          | ((sk_B_1) != (k1_relat_1 @ X29))
% 0.35/0.54          | ~ (v1_funct_1 @ X29)
% 0.35/0.54          | ~ (v1_relat_1 @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.35/0.54        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.35/0.54        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.54  thf('34', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.35/0.54        | ((sk_B_1) != (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.35/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.35/0.54  thf('37', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.35/0.54  thf('38', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.35/0.54  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['36', '39'])).
% 0.35/0.54  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ?[B:$i]:
% 0.35/0.54       ( ( ![C:$i]:
% 0.35/0.54           ( ( r2_hidden @ C @ A ) =>
% 0.35/0.54             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.35/0.54         ( v1_relat_1 @ B ) ) ))).
% 0.35/0.54  thf('41', plain, (![X25 : $i]: ((k1_relat_1 @ (sk_B @ X25)) = (X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.35/0.54  thf(t64_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X24 : $i]:
% 0.35/0.54         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.35/0.54          | ((X24) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_relat_1 @ X24))),
% 0.35/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((X0) != (k1_xboole_0))
% 0.35/0.54          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.35/0.54          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.54  thf('44', plain, (![X25 : $i]: (v1_relat_1 @ (sk_B @ X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.35/0.54  thf('47', plain, (![X25 : $i]: (v1_funct_1 @ (sk_B @ X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.35/0.54  thf('48', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.35/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.35/0.54  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['40', '48'])).
% 0.35/0.54  thf('50', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['30', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.54          | (r2_hidden @ X0 @ X2)
% 0.35/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((sk_A) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['8', '52'])).
% 0.35/0.54  thf('54', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['54'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['54'])).
% 0.35/0.54  thf('57', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['40', '48'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.54  thf('59', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['58'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.35/0.54      inference('split', [status(esa)], ['54'])).
% 0.35/0.54  thf('61', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.35/0.54  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['55', '61'])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (![X0 : $i]: (r2_hidden @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['53', '62'])).
% 0.35/0.54  thf('64', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('65', plain, ($false), inference('sup-', [status(thm)], ['63', '64'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
