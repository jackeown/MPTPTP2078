%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wuZzzYBB33

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 5.41s
% Output     : Refutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  147 (1611 expanded)
%              Number of leaves         :   27 ( 477 expanded)
%              Depth                    :   27
%              Number of atoms          : 1237 (14898 expanded)
%              Number of equality atoms :  171 (2309 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ X0 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 )
      | ( X12
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('29',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_4
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_C_4
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_C_4
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_4 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
      = ( k1_tarski @ ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_tarski @ ( k4_tarski @ X5 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('43',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','43'])).

thf('45',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_4 )
      | ( X0
        = ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( sk_C_4 = k1_xboole_0 )
    | ( ( sk_C_2 @ sk_C_4 @ k1_xboole_0 )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ sk_C_4 )
    = sk_C_4 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_C_4 @ sk_C_4 )
    = sk_C_4 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_4 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_C_4 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( sk_C_2 @ sk_C_4 @ k1_xboole_0 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 )
      | ( X12
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X29 @ X27 ) @ X29 ) @ X27 )
      | ( X28
       != ( k2_relat_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('64',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X29 @ X27 ) @ X29 ) @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
      = ( k1_tarski @ ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_tarski @ ( k4_tarski @ X5 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('71',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ( X28
       != ( k2_relat_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( sk_C_1 @ X13 @ X12 )
       != X13 )
      | ( X12
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('83',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ ( k1_tarski @ ( sk_C_2 @ sk_C_4 @ k1_xboole_0 ) ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['61','83'])).

thf('85',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_C_2 @ sk_C_4 @ k1_xboole_0 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','60'])).

thf('87',plain,
    ( sk_C_4
    = ( k1_tarski @ ( sk_C_2 @ sk_C_4 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ( sk_C_2 @ sk_C_4 @ k1_xboole_0 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','60'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('93',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_tarski @ ( k4_tarski @ X5 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('96',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('97',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','102'])).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( sk_C_1 @ X13 @ X12 )
       != X13 )
      | ( X12
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ ( k1_tarski @ ( sk_C_2 @ sk_C_4 @ k1_xboole_0 ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['91','108'])).

thf('110',plain,
    ( sk_C_4
    = ( k1_tarski @ ( sk_C_2 @ sk_C_4 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['89'])).

thf('113',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_relat_1 @ sk_C_4 ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['89'])).

thf('116',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['90','116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wuZzzYBB33
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:51:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.41/5.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.41/5.60  % Solved by: fo/fo7.sh
% 5.41/5.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.41/5.60  % done 3057 iterations in 5.148s
% 5.41/5.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.41/5.60  % SZS output start Refutation
% 5.41/5.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.41/5.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.41/5.60  thf(sk_C_4_type, type, sk_C_4: $i).
% 5.41/5.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.41/5.60  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 5.41/5.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 5.41/5.60  thf(sk_A_type, type, sk_A: $i).
% 5.41/5.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.41/5.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.41/5.60  thf(sk_B_type, type, sk_B: $i).
% 5.41/5.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.41/5.60  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 5.41/5.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.41/5.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.41/5.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.41/5.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.41/5.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.41/5.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 5.41/5.60  thf(d4_relat_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 5.41/5.60       ( ![C:$i]:
% 5.41/5.60         ( ( r2_hidden @ C @ B ) <=>
% 5.41/5.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 5.41/5.60  thf('0', plain,
% 5.41/5.60      (![X20 : $i, X23 : $i]:
% 5.41/5.60         (((X23) = (k1_relat_1 @ X20))
% 5.41/5.60          | (r2_hidden @ 
% 5.41/5.60             (k4_tarski @ (sk_C_2 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 5.41/5.60          | (r2_hidden @ (sk_C_2 @ X23 @ X20) @ X23))),
% 5.41/5.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 5.41/5.60  thf(d1_tarski, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.41/5.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.41/5.60  thf('1', plain,
% 5.41/5.60      (![X0 : $i, X4 : $i]:
% 5.41/5.60         (((X4) = (k1_tarski @ X0))
% 5.41/5.60          | ((sk_C @ X4 @ X0) = (X0))
% 5.41/5.60          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 5.41/5.60      inference('cnf', [status(esa)], [d1_tarski])).
% 5.41/5.60  thf(t46_zfmisc_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( r2_hidden @ A @ B ) =>
% 5.41/5.60       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 5.41/5.60  thf('2', plain,
% 5.41/5.60      (![X14 : $i, X15 : $i]:
% 5.41/5.60         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 5.41/5.60          | ~ (r2_hidden @ X15 @ X14))),
% 5.41/5.60      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 5.41/5.60  thf('3', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (((sk_C @ X0 @ X1) = (X1))
% 5.41/5.60          | ((X0) = (k1_tarski @ X1))
% 5.41/5.60          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ X1)) @ X0) = (X0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['1', '2'])).
% 5.41/5.60  thf(t49_zfmisc_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 5.41/5.60  thf('4', plain,
% 5.41/5.60      (![X16 : $i, X17 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 5.41/5.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.41/5.60  thf('5', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (((X0) != (k1_xboole_0))
% 5.41/5.60          | ((X0) = (k1_tarski @ X1))
% 5.41/5.60          | ((sk_C @ X0 @ X1) = (X1)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['3', '4'])).
% 5.41/5.60  thf('6', plain,
% 5.41/5.60      (![X1 : $i]:
% 5.41/5.60         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 5.41/5.60          | ((k1_xboole_0) = (k1_tarski @ X1)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['5'])).
% 5.41/5.60  thf('7', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d1_tarski])).
% 5.41/5.60  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['7'])).
% 5.41/5.60  thf('9', plain,
% 5.41/5.60      (![X14 : $i, X15 : $i]:
% 5.41/5.60         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 5.41/5.60          | ~ (r2_hidden @ X15 @ X14))),
% 5.41/5.60      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 5.41/5.60  thf('10', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 5.41/5.60           = (k1_tarski @ X0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['8', '9'])).
% 5.41/5.60  thf('11', plain,
% 5.41/5.60      (![X16 : $i, X17 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 5.41/5.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.41/5.60  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['10', '11'])).
% 5.41/5.60  thf('13', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 5.41/5.60  thf('14', plain,
% 5.41/5.60      (![X0 : $i, X4 : $i]:
% 5.41/5.60         (((X4) = (k1_tarski @ X0))
% 5.41/5.60          | ((sk_C @ X4 @ X0) != (X0))
% 5.41/5.60          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 5.41/5.60      inference('cnf', [status(esa)], [d1_tarski])).
% 5.41/5.60  thf('15', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.41/5.60          | ((sk_C @ k1_xboole_0 @ X0) != (X0))
% 5.41/5.60          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['13', '14'])).
% 5.41/5.60  thf('16', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 5.41/5.60  thf('17', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.41/5.60          | ((X0) != (X0))
% 5.41/5.60          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 5.41/5.60      inference('demod', [status(thm)], ['15', '16'])).
% 5.41/5.60  thf('18', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['17'])).
% 5.41/5.60  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['10', '11'])).
% 5.41/5.60  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 5.41/5.60  thf('21', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.41/5.60          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['0', '20'])).
% 5.41/5.60  thf(t41_zfmisc_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.41/5.60          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 5.41/5.60  thf('22', plain,
% 5.41/5.60      (![X12 : $i, X13 : $i]:
% 5.41/5.60         (((X12) = (k1_xboole_0))
% 5.41/5.60          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12)
% 5.41/5.60          | ((X12) = (k1_tarski @ X13)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 5.41/5.60  thf('23', plain,
% 5.41/5.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X22 @ X21)
% 5.41/5.60          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 5.41/5.60          | ((X21) != (k1_relat_1 @ X20)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 5.41/5.60  thf('24', plain,
% 5.41/5.60      (![X20 : $i, X22 : $i]:
% 5.41/5.60         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 5.41/5.60          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['23'])).
% 5.41/5.60  thf('25', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 5.41/5.60          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 5.41/5.60          | (r2_hidden @ 
% 5.41/5.60             (k4_tarski @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.41/5.60              (sk_D_1 @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 5.41/5.60             X0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['22', '24'])).
% 5.41/5.60  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 5.41/5.60  thf('27', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.41/5.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['25', '26'])).
% 5.41/5.60  thf('28', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.41/5.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['25', '26'])).
% 5.41/5.60  thf(t23_relat_1, conjecture,
% 5.41/5.60    (![A:$i,B:$i,C:$i]:
% 5.41/5.60     ( ( v1_relat_1 @ C ) =>
% 5.41/5.60       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 5.41/5.60         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 5.41/5.60           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 5.41/5.60  thf(zf_stmt_0, negated_conjecture,
% 5.41/5.60    (~( ![A:$i,B:$i,C:$i]:
% 5.41/5.60        ( ( v1_relat_1 @ C ) =>
% 5.41/5.60          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 5.41/5.60            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 5.41/5.60              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 5.41/5.60    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 5.41/5.60  thf('29', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('30', plain,
% 5.41/5.60      ((((sk_C_4) = (k1_relat_1 @ k1_xboole_0))
% 5.41/5.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 5.41/5.60      inference('sup+', [status(thm)], ['28', '29'])).
% 5.41/5.60  thf('31', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (((sk_C_4) = (k1_tarski @ X0))
% 5.41/5.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.41/5.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 5.41/5.60      inference('sup+', [status(thm)], ['27', '30'])).
% 5.41/5.60  thf('32', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 5.41/5.60          | ((sk_C_4) = (k1_tarski @ X0)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['31'])).
% 5.41/5.60  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['7'])).
% 5.41/5.60  thf('34', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         ((r2_hidden @ X0 @ sk_C_4)
% 5.41/5.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 5.41/5.60      inference('sup+', [status(thm)], ['32', '33'])).
% 5.41/5.60  thf('35', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf(t34_zfmisc_1, axiom,
% 5.41/5.60    (![A:$i,B:$i,C:$i,D:$i]:
% 5.41/5.60     ( ( r2_hidden @
% 5.41/5.60         ( k4_tarski @ A @ B ) @ 
% 5.41/5.60         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 5.41/5.60       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 5.41/5.60  thf('36', plain,
% 5.41/5.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.41/5.60         (((X6) = (X5))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ 
% 5.41/5.60               (k2_zfmisc_1 @ (k1_tarski @ X5) @ (k1_tarski @ X8))))),
% 5.41/5.60      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 5.41/5.60  thf(t35_zfmisc_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 5.41/5.60       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 5.41/5.60  thf('37', plain,
% 5.41/5.60      (![X10 : $i, X11 : $i]:
% 5.41/5.60         ((k2_zfmisc_1 @ (k1_tarski @ X10) @ (k1_tarski @ X11))
% 5.41/5.60           = (k1_tarski @ (k4_tarski @ X10 @ X11)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 5.41/5.60  thf('38', plain,
% 5.41/5.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.41/5.60         (((X6) = (X5))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ 
% 5.41/5.60               (k1_tarski @ (k4_tarski @ X5 @ X8))))),
% 5.41/5.60      inference('demod', [status(thm)], ['36', '37'])).
% 5.41/5.60  thf('39', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X1) = (sk_A)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['35', '38'])).
% 5.41/5.60  thf('40', plain,
% 5.41/5.60      (![X1 : $i]:
% 5.41/5.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ((X1) = (sk_A)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['34', '39'])).
% 5.41/5.60  thf('41', plain,
% 5.41/5.60      ((((sk_A) != (k1_xboole_0))
% 5.41/5.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 5.41/5.60      inference('eq_fact', [status(thm)], ['40'])).
% 5.41/5.60  thf('42', plain,
% 5.41/5.60      (![X1 : $i]:
% 5.41/5.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ((X1) = (sk_A)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['34', '39'])).
% 5.41/5.60  thf('43', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.41/5.60      inference('clc', [status(thm)], ['41', '42'])).
% 5.41/5.60  thf('44', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.41/5.60          | ((X0) = (k1_xboole_0)))),
% 5.41/5.60      inference('demod', [status(thm)], ['21', '43'])).
% 5.41/5.60  thf('45', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('46', plain,
% 5.41/5.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d1_tarski])).
% 5.41/5.60  thf('47', plain,
% 5.41/5.60      (![X0 : $i, X3 : $i]:
% 5.41/5.60         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['46'])).
% 5.41/5.60  thf('48', plain,
% 5.41/5.60      (![X0 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X0 @ sk_C_4) | ((X0) = (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['45', '47'])).
% 5.41/5.60  thf('49', plain,
% 5.41/5.60      ((((sk_C_4) = (k1_xboole_0))
% 5.41/5.60        | ((sk_C_2 @ sk_C_4 @ k1_xboole_0) = (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['44', '48'])).
% 5.41/5.60  thf('50', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['7'])).
% 5.41/5.60  thf('52', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_4)),
% 5.41/5.60      inference('sup+', [status(thm)], ['50', '51'])).
% 5.41/5.60  thf('53', plain,
% 5.41/5.60      (![X14 : $i, X15 : $i]:
% 5.41/5.60         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 5.41/5.60          | ~ (r2_hidden @ X15 @ X14))),
% 5.41/5.60      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 5.41/5.60  thf('54', plain,
% 5.41/5.60      (((k2_xboole_0 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ sk_C_4)
% 5.41/5.60         = (sk_C_4))),
% 5.41/5.60      inference('sup-', [status(thm)], ['52', '53'])).
% 5.41/5.60  thf('55', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('56', plain, (((k2_xboole_0 @ sk_C_4 @ sk_C_4) = (sk_C_4))),
% 5.41/5.60      inference('demod', [status(thm)], ['54', '55'])).
% 5.41/5.60  thf('57', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('58', plain,
% 5.41/5.60      (![X16 : $i, X17 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 5.41/5.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.41/5.60  thf('59', plain,
% 5.41/5.60      (![X0 : $i]: ((k2_xboole_0 @ sk_C_4 @ X0) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['57', '58'])).
% 5.41/5.60  thf('60', plain, (((sk_C_4) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['56', '59'])).
% 5.41/5.60  thf('61', plain,
% 5.41/5.60      (((sk_C_2 @ sk_C_4 @ k1_xboole_0) = (k4_tarski @ sk_A @ sk_B))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['49', '60'])).
% 5.41/5.60  thf('62', plain,
% 5.41/5.60      (![X12 : $i, X13 : $i]:
% 5.41/5.60         (((X12) = (k1_xboole_0))
% 5.41/5.60          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12)
% 5.41/5.60          | ((X12) = (k1_tarski @ X13)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 5.41/5.60  thf(d5_relat_1, axiom,
% 5.41/5.60    (![A:$i,B:$i]:
% 5.41/5.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 5.41/5.60       ( ![C:$i]:
% 5.41/5.60         ( ( r2_hidden @ C @ B ) <=>
% 5.41/5.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 5.41/5.60  thf('63', plain,
% 5.41/5.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.41/5.60         (~ (r2_hidden @ X29 @ X28)
% 5.41/5.60          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X29 @ X27) @ X29) @ X27)
% 5.41/5.60          | ((X28) != (k2_relat_1 @ X27)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 5.41/5.60  thf('64', plain,
% 5.41/5.60      (![X27 : $i, X29 : $i]:
% 5.41/5.60         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X29 @ X27) @ X29) @ X27)
% 5.41/5.60          | ~ (r2_hidden @ X29 @ (k2_relat_1 @ X27)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['63'])).
% 5.41/5.60  thf('65', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 5.41/5.60          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 5.41/5.60          | (r2_hidden @ 
% 5.41/5.60             (k4_tarski @ (sk_D_3 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 5.41/5.60              (sk_C_1 @ X1 @ (k2_relat_1 @ X0))) @ 
% 5.41/5.60             X0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['62', '64'])).
% 5.41/5.60  thf('66', plain,
% 5.41/5.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.41/5.60         (((X7) = (X8))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ 
% 5.41/5.60               (k2_zfmisc_1 @ (k1_tarski @ X5) @ (k1_tarski @ X8))))),
% 5.41/5.60      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 5.41/5.60  thf('67', plain,
% 5.41/5.60      (![X10 : $i, X11 : $i]:
% 5.41/5.60         ((k2_zfmisc_1 @ (k1_tarski @ X10) @ (k1_tarski @ X11))
% 5.41/5.60           = (k1_tarski @ (k4_tarski @ X10 @ X11)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 5.41/5.60  thf('68', plain,
% 5.41/5.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.41/5.60         (((X7) = (X8))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ 
% 5.41/5.60               (k1_tarski @ (k4_tarski @ X5 @ X8))))),
% 5.41/5.60      inference('demod', [status(thm)], ['66', '67'])).
% 5.41/5.60  thf('69', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_xboole_0))
% 5.41/5.60          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 5.41/5.60              = (k1_tarski @ X2))
% 5.41/5.60          | ((sk_C_1 @ X2 @ (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60              = (X0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['65', '68'])).
% 5.41/5.60  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['7'])).
% 5.41/5.60  thf('71', plain,
% 5.41/5.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.41/5.60         (~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ X27)
% 5.41/5.60          | (r2_hidden @ X26 @ X28)
% 5.41/5.60          | ((X28) != (k2_relat_1 @ X27)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 5.41/5.60  thf('72', plain,
% 5.41/5.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.41/5.60         ((r2_hidden @ X26 @ (k2_relat_1 @ X27))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ X27))),
% 5.41/5.60      inference('simplify', [status(thm)], ['71'])).
% 5.41/5.60  thf('73', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (r2_hidden @ X0 @ (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 5.41/5.60      inference('sup-', [status(thm)], ['70', '72'])).
% 5.41/5.60  thf('74', plain,
% 5.41/5.60      (![X14 : $i, X15 : $i]:
% 5.41/5.60         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 5.41/5.60          | ~ (r2_hidden @ X15 @ X14))),
% 5.41/5.60      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 5.41/5.60  thf('75', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ 
% 5.41/5.60           (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60           = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 5.41/5.60      inference('sup-', [status(thm)], ['73', '74'])).
% 5.41/5.60  thf('76', plain,
% 5.41/5.60      (![X16 : $i, X17 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 5.41/5.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.41/5.60  thf('77', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['75', '76'])).
% 5.41/5.60  thf('78', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 5.41/5.60            = (k1_tarski @ X2))
% 5.41/5.60          | ((sk_C_1 @ X2 @ (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60              = (X0)))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['69', '77'])).
% 5.41/5.60  thf('79', plain,
% 5.41/5.60      (![X12 : $i, X13 : $i]:
% 5.41/5.60         (((X12) = (k1_xboole_0))
% 5.41/5.60          | ((sk_C_1 @ X13 @ X12) != (X13))
% 5.41/5.60          | ((X12) = (k1_tarski @ X13)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 5.41/5.60  thf('80', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((X0) != (X1))
% 5.41/5.60          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X0)))
% 5.41/5.60              = (k1_tarski @ X1))
% 5.41/5.60          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X0)))
% 5.41/5.60              = (k1_tarski @ X1))
% 5.41/5.60          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X0))) = (k1_xboole_0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['78', '79'])).
% 5.41/5.60  thf('81', plain,
% 5.41/5.60      (![X1 : $i, X2 : $i]:
% 5.41/5.60         (((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))) = (k1_xboole_0))
% 5.41/5.60          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 5.41/5.60              = (k1_tarski @ X1)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['80'])).
% 5.41/5.60  thf('82', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['75', '76'])).
% 5.41/5.60  thf('83', plain,
% 5.41/5.60      (![X1 : $i, X2 : $i]:
% 5.41/5.60         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))) = (k1_tarski @ X1))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 5.41/5.60  thf('84', plain,
% 5.41/5.60      (((k2_relat_1 @ (k1_tarski @ (sk_C_2 @ sk_C_4 @ k1_xboole_0)))
% 5.41/5.60         = (k1_tarski @ sk_B))),
% 5.41/5.60      inference('sup+', [status(thm)], ['61', '83'])).
% 5.41/5.60  thf('85', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('86', plain,
% 5.41/5.60      (((sk_C_2 @ sk_C_4 @ k1_xboole_0) = (k4_tarski @ sk_A @ sk_B))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['49', '60'])).
% 5.41/5.60  thf('87', plain,
% 5.41/5.60      (((sk_C_4) = (k1_tarski @ (sk_C_2 @ sk_C_4 @ k1_xboole_0)))),
% 5.41/5.60      inference('demod', [status(thm)], ['85', '86'])).
% 5.41/5.60  thf('88', plain, (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))),
% 5.41/5.60      inference('demod', [status(thm)], ['84', '87'])).
% 5.41/5.60  thf('89', plain,
% 5.41/5.60      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A))
% 5.41/5.60        | ((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))),
% 5.41/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.60  thf('90', plain,
% 5.41/5.60      ((((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))
% 5.41/5.60         <= (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))))),
% 5.41/5.60      inference('split', [status(esa)], ['89'])).
% 5.41/5.60  thf('91', plain,
% 5.41/5.60      (((sk_C_2 @ sk_C_4 @ k1_xboole_0) = (k4_tarski @ sk_A @ sk_B))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['49', '60'])).
% 5.41/5.60  thf('92', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 5.41/5.60          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 5.41/5.60          | (r2_hidden @ 
% 5.41/5.60             (k4_tarski @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.41/5.60              (sk_D_1 @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 5.41/5.60             X0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['22', '24'])).
% 5.41/5.60  thf('93', plain,
% 5.41/5.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.41/5.60         (((X6) = (X5))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ 
% 5.41/5.60               (k1_tarski @ (k4_tarski @ X5 @ X8))))),
% 5.41/5.60      inference('demod', [status(thm)], ['36', '37'])).
% 5.41/5.60  thf('94', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_xboole_0))
% 5.41/5.60          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 5.41/5.60              = (k1_tarski @ X2))
% 5.41/5.60          | ((sk_C_1 @ X2 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60              = (X1)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['92', '93'])).
% 5.41/5.60  thf('95', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.41/5.60      inference('simplify', [status(thm)], ['7'])).
% 5.41/5.60  thf('96', plain,
% 5.41/5.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 5.41/5.60         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 5.41/5.60          | (r2_hidden @ X18 @ X21)
% 5.41/5.60          | ((X21) != (k1_relat_1 @ X20)))),
% 5.41/5.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 5.41/5.60  thf('97', plain,
% 5.41/5.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.41/5.60         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 5.41/5.60          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 5.41/5.60      inference('simplify', [status(thm)], ['96'])).
% 5.41/5.60  thf('98', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         (r2_hidden @ X1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 5.41/5.60      inference('sup-', [status(thm)], ['95', '97'])).
% 5.41/5.60  thf('99', plain,
% 5.41/5.60      (![X14 : $i, X15 : $i]:
% 5.41/5.60         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 5.41/5.60          | ~ (r2_hidden @ X15 @ X14))),
% 5.41/5.60      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 5.41/5.60  thf('100', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X1) @ 
% 5.41/5.60           (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60           = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 5.41/5.60      inference('sup-', [status(thm)], ['98', '99'])).
% 5.41/5.60  thf('101', plain,
% 5.41/5.60      (![X16 : $i, X17 : $i]:
% 5.41/5.60         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 5.41/5.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.41/5.60  thf('102', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['100', '101'])).
% 5.41/5.60  thf('103', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 5.41/5.60            = (k1_tarski @ X2))
% 5.41/5.60          | ((sk_C_1 @ X2 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 5.41/5.60              = (X1)))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['94', '102'])).
% 5.41/5.60  thf('104', plain,
% 5.41/5.60      (![X12 : $i, X13 : $i]:
% 5.41/5.60         (((X12) = (k1_xboole_0))
% 5.41/5.60          | ((sk_C_1 @ X13 @ X12) != (X13))
% 5.41/5.60          | ((X12) = (k1_tarski @ X13)))),
% 5.41/5.60      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 5.41/5.60  thf('105', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.60         (((X0) != (X1))
% 5.41/5.60          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2)))
% 5.41/5.60              = (k1_tarski @ X1))
% 5.41/5.60          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2)))
% 5.41/5.60              = (k1_tarski @ X1))
% 5.41/5.60          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2))) = (k1_xboole_0)))),
% 5.41/5.60      inference('sup-', [status(thm)], ['103', '104'])).
% 5.41/5.60  thf('106', plain,
% 5.41/5.60      (![X1 : $i, X2 : $i]:
% 5.41/5.60         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X2))) = (k1_xboole_0))
% 5.41/5.60          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X2)))
% 5.41/5.60              = (k1_tarski @ X1)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['105'])).
% 5.41/5.60  thf('107', plain,
% 5.41/5.60      (![X0 : $i, X1 : $i]:
% 5.41/5.60         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) != (k1_xboole_0))),
% 5.41/5.60      inference('sup-', [status(thm)], ['100', '101'])).
% 5.41/5.60  thf('108', plain,
% 5.41/5.60      (![X1 : $i, X2 : $i]:
% 5.41/5.60         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X2))) = (k1_tarski @ X1))),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 5.41/5.60  thf('109', plain,
% 5.41/5.60      (((k1_relat_1 @ (k1_tarski @ (sk_C_2 @ sk_C_4 @ k1_xboole_0)))
% 5.41/5.60         = (k1_tarski @ sk_A))),
% 5.41/5.60      inference('sup+', [status(thm)], ['91', '108'])).
% 5.41/5.60  thf('110', plain,
% 5.41/5.60      (((sk_C_4) = (k1_tarski @ (sk_C_2 @ sk_C_4 @ k1_xboole_0)))),
% 5.41/5.60      inference('demod', [status(thm)], ['85', '86'])).
% 5.41/5.60  thf('111', plain, (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))),
% 5.41/5.60      inference('demod', [status(thm)], ['109', '110'])).
% 5.41/5.60  thf('112', plain,
% 5.41/5.60      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A)))
% 5.41/5.60         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 5.41/5.60      inference('split', [status(esa)], ['89'])).
% 5.41/5.60  thf('113', plain,
% 5.41/5.60      ((((k1_relat_1 @ sk_C_4) != (k1_relat_1 @ sk_C_4)))
% 5.41/5.60         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 5.41/5.60      inference('sup-', [status(thm)], ['111', '112'])).
% 5.41/5.60  thf('114', plain, ((((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 5.41/5.60      inference('simplify', [status(thm)], ['113'])).
% 5.41/5.60  thf('115', plain,
% 5.41/5.60      (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))) | 
% 5.41/5.60       ~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 5.41/5.60      inference('split', [status(esa)], ['89'])).
% 5.41/5.60  thf('116', plain, (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 5.41/5.60      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 5.41/5.60  thf('117', plain, (((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B))),
% 5.41/5.60      inference('simpl_trail', [status(thm)], ['90', '116'])).
% 5.41/5.60  thf('118', plain, ($false),
% 5.41/5.60      inference('simplify_reflect-', [status(thm)], ['88', '117'])).
% 5.41/5.60  
% 5.41/5.60  % SZS output end Refutation
% 5.41/5.60  
% 5.41/5.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
