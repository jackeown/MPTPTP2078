%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bCWkdgSVj4

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 190 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  579 ( 961 expanded)
%              Number of equality atoms :   73 ( 130 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28
        = ( k1_relat_1 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X28 @ X25 ) @ ( sk_D @ X28 @ X25 ) ) @ X25 )
      | ( r2_hidden @ ( sk_C_2 @ X28 @ X25 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('14',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ o_0_0_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X32 @ X31 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

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

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X13: $i] :
      ( ( X13 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k5_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ o_0_0_xboole_0 )
      = X20 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('44',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('48',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('54',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('58',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','60'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','65'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','68'])).

thf('70',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('71',plain,(
    ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','71'])).

thf('73',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bCWkdgSVj4
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 193 iterations in 0.050s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(cc1_relat_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.49  thf(d4_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X25 : $i, X28 : $i]:
% 0.20/0.49         (((X28) = (k1_relat_1 @ X25))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_C_2 @ X28 @ X25) @ (sk_D @ X28 @ X25)) @ X25)
% 0.20/0.49          | (r2_hidden @ (sk_C_2 @ X28 @ X25) @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.49  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X17 : $i]: ((k3_xboole_0 @ X17 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.49  thf(t4_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.20/0.49          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ o_0_0_xboole_0)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.49  thf('8', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.49  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('10', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_2 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.20/0.49          | ((X0) = (k1_relat_1 @ o_0_0_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.49  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf('14', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf(t37_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X33 : $i]:
% 0.20/0.49         (((k1_relat_1 @ X33) = (k2_relat_1 @ (k4_relat_1 @ X33)))
% 0.20/0.49          | ~ (v1_relat_1 @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.49  thf('16', plain, (![X22 : $i]: ((v1_relat_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.49  thf(t1_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('18', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.49  thf('19', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X16 : $i]: ((k2_xboole_0 @ X16 @ o_0_0_xboole_0) = (X16))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.49  thf(t26_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.49             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X31)
% 0.20/0.49          | ((k2_relat_1 @ (k2_xboole_0 @ X32 @ X31))
% 0.20/0.49              = (k2_xboole_0 @ (k2_relat_1 @ X32) @ (k2_relat_1 @ X31)))
% 0.20/0.49          | ~ (v1_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.20/0.49  thf(t3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(t7_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         (((X13) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.20/0.49          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.20/0.49          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X14 @ X15)
% 0.20/0.49           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf(t5_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('34', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.49  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X20 : $i]: ((k5_xboole_0 @ X20 @ o_0_0_xboole_0) = (X20))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.49  thf(t46_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.49  thf('39', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['37', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k2_relat_1 @ X1) = (o_0_0_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.20/0.49          | ((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '42'])).
% 0.20/0.49  thf(t60_relat_1, conjecture,
% 0.20/0.49    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('46', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('47', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.49         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.49  thf('49', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('50', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((((k1_relat_1 @ o_0_0_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((k1_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '54'])).
% 0.20/0.49  thf('56', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.49       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('58', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain, (((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['48', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['43', '59'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '60'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('63', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('64', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['61', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '65'])).
% 0.20/0.49  thf(dt_k4_relat_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (![X30 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X30)) | ~ (v1_relat_1 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ o_0_0_xboole_0) | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '68'])).
% 0.20/0.49  thf('70', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('71', plain, (~ (v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, (~ (v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '71'])).
% 0.20/0.49  thf('73', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('74', plain, ($false), inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
