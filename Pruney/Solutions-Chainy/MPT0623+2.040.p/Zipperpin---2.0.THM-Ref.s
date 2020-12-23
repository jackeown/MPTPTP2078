%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBB2RGFQfj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 191 expanded)
%              Number of leaves         :   32 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  842 (1640 expanded)
%              Number of equality atoms :  134 ( 274 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X26 @ X27 ) )
        = X27 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

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
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
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

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('36',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('37',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

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

thf('40',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('47',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','51'])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('56',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('63',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64','69'])).

thf('71',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('73',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('74',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('76',plain,
    ( ( sk_B_1
      = ( k6_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('81',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('82',plain,
    ( ( ( sk_B @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('84',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('86',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['79','86'])).

thf('88',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['52','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('93',plain,(
    $false ),
    inference('sup-',[status(thm)],['91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBB2RGFQfj
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 124 iterations in 0.065s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(d5_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.22/0.50         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.22/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.22/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.50  thf(t113_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 0.22/0.50          | ((X19) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.50  thf(t152_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i]: ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.50  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.50          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.50  thf(t4_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.50          | ((X1) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t15_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ?[C:$i]:
% 0.22/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.22/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (sk_C_2 @ X26 @ X27)) = (X27))
% 0.22/0.50          | ((X27) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         ((v1_relat_1 @ (sk_C_2 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (sk_C_2 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.22/0.50          | ((X15) = (X12))
% 0.22/0.50          | ((X14) != (k1_tarski @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X12 : $i, X15 : $i]:
% 0.22/0.50         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ X0 @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         (((k2_relat_1 @ (sk_C_2 @ X26 @ X27)) = (k1_tarski @ X26))
% 0.22/0.50          | ((X27) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf(t18_funct_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.50                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.50                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X28 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.22/0.50          | ~ (v1_funct_1 @ X28)
% 0.22/0.50          | ~ (v1_relat_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.22/0.50          | ((X1) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.22/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_A @ X0)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.22/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.22/0.50          | ((X1) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X0) = (k1_xboole_0))
% 0.22/0.50          | ((X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_A @ X1)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X0) = (k1_xboole_0))
% 0.22/0.50          | ((X0) = (k1_xboole_0))
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_A @ X1)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((sk_B_1) != (X0))
% 0.22/0.50          | ((X0) = (k1_xboole_0))
% 0.22/0.50          | ((X0) = (k1_xboole_0))
% 0.22/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X28 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.22/0.50          | ~ (v1_funct_1 @ X28)
% 0.22/0.50          | ~ (v1_relat_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.22/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('33', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50        | ((sk_B_1) != (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.50  thf('36', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.50  thf('37', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.50  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '38'])).
% 0.22/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ?[B:$i]:
% 0.22/0.50       ( ( ![C:$i]:
% 0.22/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.22/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.22/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.22/0.50  thf('40', plain, (![X24 : $i]: ((k1_relat_1 @ (sk_B @ X24)) = (X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf(t64_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X23 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.22/0.50          | ((X23) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X23))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) != (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.22/0.50          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain, (![X24 : $i]: (v1_relat_1 @ (sk_B @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.50  thf('45', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.50  thf('46', plain, (![X24 : $i]: (v1_funct_1 @ (sk_B @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('47', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['39', '47'])).
% 0.22/0.50  thf('49', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['29', '48'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((sk_A) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '51'])).
% 0.22/0.50  thf('53', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('56', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['55', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X28 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.22/0.50          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.22/0.50          | ~ (v1_funct_1 @ X28)
% 0.22/0.50          | ~ (v1_relat_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.50         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('63', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.50         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '64', '69'])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('73', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.22/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['72', '73'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      ((((sk_B_1) = (k6_relat_1 @ sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.50  thf('78', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['76', '77'])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['71', '78'])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('81', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.50  thf('82', plain,
% 0.22/0.50      ((((sk_B @ sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['80', '81'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.50  thf('85', plain, (![X24 : $i]: (v1_funct_1 @ (sk_B @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('86', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['84', '85'])).
% 0.22/0.50  thf('87', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['79', '86'])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['53'])).
% 0.22/0.50  thf('89', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.22/0.50  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['54', '89'])).
% 0.22/0.50  thf('91', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['52', '90'])).
% 0.22/0.50  thf('92', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('93', plain, ($false), inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
