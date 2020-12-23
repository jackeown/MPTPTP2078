%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4emVLBk3rU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 (1598 expanded)
%              Number of leaves         :   28 ( 466 expanded)
%              Depth                    :   28
%              Number of atoms          : 1074 (16176 expanded)
%              Number of equality atoms :  154 (2358 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X26 @ X27 ) )
        = X27 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X26 @ X27 ) )
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 ) ) ),
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

thf('16',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

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

thf('31',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','38'])).

thf('40',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('41',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('42',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['24','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_A @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ sk_A ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_A @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ sk_A ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('50',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ sk_A ) ) )
      | ( ( sk_D @ k1_xboole_0 @ sk_A @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ sk_A ) ) )
      | ( ( sk_D @ k1_xboole_0 @ sk_A @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ sk_A ) ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_A @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('73',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('77',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','74','79'])).

thf('81',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('83',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('93',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('95',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('96',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('97',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['64','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['62','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('104',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('105',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X0 )
      | ( sk_A
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['62','101'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['62','101'])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('110',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['64','100'])).

thf('112',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4emVLBk3rU
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 119 iterations in 0.086s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(d4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t15_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ?[C:$i]:
% 0.20/0.52           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.52             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (sk_C_2 @ X26 @ X27)) = (X27))
% 0.20/0.52          | ((X27) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (sk_C_2 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (sk_C_2 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(d1_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.52          | ((X17) = (X14))
% 0.20/0.52          | ((X16) != (k1_tarski @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X14 : $i, X17 : $i]:
% 0.20/0.52         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (sk_C_2 @ X26 @ X27)) = (k1_tarski @ X26))
% 0.20/0.52          | ((X27) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf(t18_funct_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.52                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.52                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X28 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.20/0.52          | ~ (v1_funct_1 @ X28)
% 0.20/0.52          | ~ (v1_relat_1 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_A @ X0)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.52          | ((X1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.52          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_A @ X1)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.52          | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.52          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_A @ X1)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.52          | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((sk_B_1) != (X0))
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.52  thf(t60_relat_1, axiom,
% 0.20/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('25', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X28 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.20/0.52          | ~ (v1_funct_1 @ X28)
% 0.20/0.52          | ~ (v1_relat_1 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.52        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.52        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.52        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('28', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.52        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.52        | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.52  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ?[B:$i]:
% 0.20/0.52       ( ( ![C:$i]:
% 0.20/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.52  thf('31', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B @ X22)) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf(t64_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X21 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.52          | ((X21) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) != (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.52          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.52  thf('37', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '38'])).
% 0.20/0.52  thf('40', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.52  thf('41', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('42', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '42'])).
% 0.20/0.52  thf('44', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['24', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.20/0.52          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X0 @ sk_A @ X1) @ X0)
% 0.20/0.52          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ sk_A))))),
% 0.20/0.52      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X0 @ sk_A @ X1) @ X0)
% 0.20/0.52          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ sk_A))))),
% 0.20/0.52      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.52  thf('50', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))
% 0.20/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_A @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X14 : $i, X17 : $i]:
% 0.20/0.52         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X1 @ sk_A)))
% 0.20/0.52          | ((sk_D @ k1_xboole_0 @ sk_A @ X1) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X1 @ sk_A)))
% 0.20/0.52          | ((sk_D @ k1_xboole_0 @ sk_A @ X1) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (X1))
% 0.20/0.52          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X2 @ sk_A)))
% 0.20/0.52          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X2 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X2 @ sk_A)))
% 0.20/0.52          | ((X0) = (X1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))),
% 0.20/0.52      inference('condensation', [status(thm)], ['58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X0 @ sk_A @ X1) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['48', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((sk_A) = (k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X28 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.20/0.52          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.20/0.52          | ~ (v1_funct_1 @ X28)
% 0.20/0.52          | ~ (v1_relat_1 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.52         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.52         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.52         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('73', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.52         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.52         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['71', '74', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['80'])).
% 0.20/0.52  thf('82', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B @ X22)) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (![X21 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.52          | ((X21) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.52           | ~ (v1_relat_1 @ X0)
% 0.20/0.52           | ((X0) = (k1_xboole_0))))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.52           | ~ (v1_relat_1 @ X0)
% 0.20/0.52           | ((X0) = (sk_B_1))))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((X0) != (sk_B_1))
% 0.20/0.52           | ((sk_B @ X0) = (sk_B_1))
% 0.20/0.52           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '87'])).
% 0.20/0.52  thf('89', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.20/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.52  thf('92', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('93', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['81', '93'])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.52  thf('96', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B @ X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.52  thf('97', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['95', '96'])).
% 0.20/0.52  thf('98', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['94', '97'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['63'])).
% 0.20/0.52  thf('100', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.20/0.52  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['64', '100'])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['62', '101'])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.52      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X0)
% 0.20/0.52          | ((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['102', '105'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['62', '101'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['62', '101'])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      (![X0 : $i]: ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))),
% 0.20/0.53      inference('condensation', [status(thm)], ['58'])).
% 0.20/0.53  thf('110', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.20/0.53  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['64', '100'])).
% 0.20/0.53  thf('112', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
