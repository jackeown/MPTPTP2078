%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C7vg5KZMfC

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:21 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 253 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  628 (1977 expanded)
%              Number of equality atoms :   47 ( 201 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X40: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X40 ) @ ( sk_C_1 @ X40 ) ) @ X40 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_2 ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('9',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X25 )
      | ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) )
    | ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k9_relat_1 @ X38 @ X39 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    | ( v1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    | ( v1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X40: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X40 ) @ ( sk_C_1 @ X40 ) ) @ X40 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_C_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C7vg5KZMfC
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 970 iterations in 0.530s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.76/0.98  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.98  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(t152_relat_1, conjecture,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.98            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.76/0.98            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i]:
% 0.76/0.98        ( ( v1_relat_1 @ B ) =>
% 0.76/0.98          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.98               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.76/0.98               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.76/0.98  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t37_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      (![X17 : $i, X19 : $i]:
% 0.76/0.98         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 0.76/0.98          | ~ (r1_tarski @ X17 @ X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_2)) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.98  thf(t56_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.76/0.98         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      (![X40 : $i]:
% 0.76/0.98         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X40) @ (sk_C_1 @ X40)) @ X40)
% 0.76/0.98          | ((X40) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X40))),
% 0.76/0.98      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.76/0.98  thf(d5_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.98       ( ![D:$i]:
% 0.76/0.98         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.98           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X6 @ X7)
% 0.76/0.98          | (r2_hidden @ X6 @ X8)
% 0.76/0.98          | (r2_hidden @ X6 @ X9)
% 0.76/0.98          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.76/0.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.98         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.76/0.98          | (r2_hidden @ X6 @ X8)
% 0.76/0.98          | ~ (r2_hidden @ X6 @ X7))),
% 0.76/0.98      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X0)
% 0.76/0.98          | ((X0) = (k1_xboole_0))
% 0.76/0.98          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0)) @ X1)
% 0.76/0.98          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0)) @ 
% 0.76/0.98             (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '5'])).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98         k1_xboole_0)
% 0.76/0.98        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98           (k1_relat_1 @ sk_B_2))
% 0.76/0.98        | ((sk_A) = (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('sup+', [status(thm)], ['2', '6'])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_2)) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.98  thf(d1_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) <=>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ~( ( r2_hidden @ B @ A ) & 
% 0.76/0.98              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.76/0.98  thf('9', plain,
% 0.76/0.98      (![X29 : $i]: ((v1_relat_1 @ X29) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.76/0.98      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.98         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.76/0.98          | (r2_hidden @ X6 @ X8)
% 0.76/0.98          | ~ (r2_hidden @ X6 @ X7))),
% 0.76/0.98      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_relat_1 @ X0)
% 0.76/0.98          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.76/0.98          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      (((r2_hidden @ (sk_B @ sk_A) @ k1_xboole_0)
% 0.76/0.98        | (r2_hidden @ (sk_B @ sk_A) @ (k1_relat_1 @ sk_B_2))
% 0.76/0.98        | (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('sup+', [status(thm)], ['8', '11'])).
% 0.76/0.98  thf(t4_boole, axiom,
% 0.76/0.98    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_boole])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((r1_tarski @ X17 @ X18)
% 0.76/0.98          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('simplify', [status(thm)], ['15'])).
% 0.76/0.98  thf(t12_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X15 : $i, X16 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf(t40_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (![X20 : $i, X21 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.76/0.98           = (k4_xboole_0 @ X20 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_boole])).
% 0.76/0.98  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf(t64_zfmisc_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.76/0.98       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.98         (((X23) != (X25))
% 0.76/0.98          | ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25))))),
% 0.76/0.98      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X24 : $i, X25 : $i]:
% 0.76/0.98         ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25)))),
% 0.76/0.98      inference('simplify', [status(thm)], ['23'])).
% 0.76/0.98  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '24'])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (((v1_relat_1 @ sk_A)
% 0.76/0.98        | (r2_hidden @ (sk_B @ sk_A) @ (k1_relat_1 @ sk_B_2)))),
% 0.76/0.98      inference('clc', [status(thm)], ['12', '25'])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X29 : $i]: ((v1_relat_1 @ X29) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.76/0.98      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.76/0.98  thf(d4_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.76/0.98       ( ![D:$i]:
% 0.76/0.98         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.98           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X0 @ X1)
% 0.76/0.98          | ~ (r2_hidden @ X0 @ X2)
% 0.76/0.98          | (r2_hidden @ X0 @ X3)
% 0.76/0.98          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.76/0.98      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.76/0.98          | ~ (r2_hidden @ X0 @ X2)
% 0.76/0.98          | ~ (r2_hidden @ X0 @ X1))),
% 0.76/0.98      inference('simplify', [status(thm)], ['28'])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_relat_1 @ X0)
% 0.76/0.98          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.76/0.98          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['27', '29'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (((v1_relat_1 @ sk_A)
% 0.76/0.98        | (r2_hidden @ (sk_B @ sk_A) @ 
% 0.76/0.98           (k3_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A))
% 0.76/0.98        | (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['26', '30'])).
% 0.76/0.98  thf('32', plain, (((k9_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t151_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.98         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      (![X38 : $i, X39 : $i]:
% 0.76/0.98         (((k9_relat_1 @ X38 @ X39) != (k1_xboole_0))
% 0.76/0.98          | (r1_xboole_0 @ (k1_relat_1 @ X38) @ X39)
% 0.76/0.98          | ~ (v1_relat_1 @ X38))),
% 0.76/0.98      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_B_2)
% 0.76/0.98        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.98  thf('35', plain, ((v1_relat_1 @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.98  thf('37', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A)),
% 0.76/0.98      inference('simplify', [status(thm)], ['36'])).
% 0.76/0.98  thf(d7_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.76/0.98       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i]:
% 0.76/0.98         (((k3_xboole_0 @ X12 @ X13) = (k1_xboole_0))
% 0.76/0.98          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (((k3_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (((v1_relat_1 @ sk_A)
% 0.76/0.98        | (r2_hidden @ (sk_B @ sk_A) @ k1_xboole_0)
% 0.76/0.98        | (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['31', '39'])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      (((r2_hidden @ (sk_B @ sk_A) @ k1_xboole_0) | (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['40'])).
% 0.76/0.98  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '24'])).
% 0.76/0.98  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('clc', [status(thm)], ['41', '42'])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98         k1_xboole_0)
% 0.76/0.98        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98           (k1_relat_1 @ sk_B_2))
% 0.76/0.98        | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['7', '43'])).
% 0.76/0.98  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      (((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98         k1_xboole_0)
% 0.76/0.98        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98           (k1_relat_1 @ sk_B_2)))),
% 0.76/0.98      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.76/0.98  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '24'])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      ((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98        (k1_relat_1 @ sk_B_2))),
% 0.76/0.98      inference('clc', [status(thm)], ['46', '47'])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X40 : $i]:
% 0.76/0.98         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X40) @ (sk_C_1 @ X40)) @ X40)
% 0.76/0.98          | ((X40) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X40))),
% 0.76/0.98      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.76/0.98          | ~ (r2_hidden @ X0 @ X2)
% 0.76/0.98          | ~ (r2_hidden @ X0 @ X1))),
% 0.76/0.98      inference('simplify', [status(thm)], ['28'])).
% 0.76/0.98  thf('51', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X0)
% 0.76/0.98          | ((X0) = (k1_xboole_0))
% 0.76/0.98          | ~ (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0)) @ X1)
% 0.76/0.98          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_C_1 @ X0)) @ 
% 0.76/0.98             (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/0.98  thf('52', plain,
% 0.76/0.98      (((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98         (k3_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A))
% 0.76/0.98        | ((sk_A) = (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['48', '51'])).
% 0.76/0.98  thf('53', plain,
% 0.76/0.98      (((k3_xboole_0 @ (k1_relat_1 @ sk_B_2) @ sk_A) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.98  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('clc', [status(thm)], ['41', '42'])).
% 0.76/0.98  thf('55', plain,
% 0.76/0.98      (((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98         k1_xboole_0)
% 0.76/0.98        | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.76/0.98  thf('56', plain, (((sk_A) != (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      ((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_C_1 @ sk_A)) @ 
% 0.76/0.98        k1_xboole_0)),
% 0.76/0.98      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.76/0.98  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '24'])).
% 0.76/0.98  thf('59', plain, ($false), inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
