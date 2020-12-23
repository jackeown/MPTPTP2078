%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.trbGlVD5BD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 160 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  666 (1336 expanded)
%              Number of equality atoms :   90 ( 201 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X29 @ X30 ) )
        = X30 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X29 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
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

thf('6',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
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

thf('16',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X29 @ X30 ) )
        = ( k1_tarski @ X29 ) )
      | ( X30 = k1_xboole_0 ) ) ),
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

thf('24',plain,(
    ! [X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('31',plain,(
    ! [X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

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

thf('36',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( sk_B @ X27 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( sk_B @ X27 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','43'])).

thf('45',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('46',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( sk_B @ X27 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('47',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X29 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.trbGlVD5BD
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 120 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(t15_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ?[C:$i]:
% 0.20/0.51           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.51             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.51             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (sk_C_3 @ X29 @ X30)) = (X30))
% 0.20/0.51          | ((X30) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (sk_C_3 @ X29 @ X30)) | ((X30) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf(d4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.51         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf(t12_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.51         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t2_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf(t4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.20/0.51          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.51  thf('8', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.51  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.51          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X14 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X14 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.51          | ((X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X20 @ X19)
% 0.20/0.51          | ((X20) = (X17))
% 0.20/0.51          | ((X19) != (k1_tarski @ X17)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X17 : $i, X20 : $i]:
% 0.20/0.51         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (sk_C_3 @ X29 @ X30)) = (k1_tarski @ X29))
% 0.20/0.51          | ((X30) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf(t18_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.51                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.51                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X31) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X31))
% 0.20/0.51          | ~ (v1_funct_1 @ X31)
% 0.20/0.51          | ~ (v1_relat_1 @ X31))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_A) = (k1_xboole_0))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1)))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))
% 0.20/0.51          | ((X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.51  thf('27', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['27'])).
% 0.20/0.51  thf(t60_relat_1, axiom,
% 0.20/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X31) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X31))
% 0.20/0.51          | ~ (v1_funct_1 @ X31)
% 0.20/0.51          | ~ (v1_relat_1 @ X31))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('33', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51        | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ?[B:$i]:
% 0.20/0.51       ( ( ![C:$i]:
% 0.20/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.51  thf('36', plain, (![X27 : $i]: ((k1_relat_1 @ (sk_B @ X27)) = (X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf(t64_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 0.20/0.51          | ((X26) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) != (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.51          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, (![X27 : $i]: (v1_relat_1 @ (sk_B @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.51  thf('42', plain, (![X27 : $i]: (v1_relat_1 @ (sk_B @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '43'])).
% 0.20/0.51  thf('45', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.51  thf('46', plain, (![X27 : $i]: (v1_funct_1 @ (sk_B @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('47', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '48'])).
% 0.20/0.51  thf('50', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['27'])).
% 0.20/0.51  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['28', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_B_1)
% 0.20/0.51            != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1)))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))
% 0.20/0.51          | ((X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['26', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ X0))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_B_1)
% 0.20/0.51            != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ X0)))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (sk_C_3 @ X29 @ X30)) | ((X30) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ X0))))),
% 0.20/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '58'])).
% 0.20/0.51  thf('60', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.51  thf('61', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.51  thf('62', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
