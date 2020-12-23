%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6yIjDXXrA0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:24 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  145 (4938 expanded)
%              Number of leaves         :   27 (1588 expanded)
%              Depth                    :   54
%              Number of atoms          : 1089 (44303 expanded)
%              Number of equality atoms :   91 (3021 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37
        = ( k1_relat_1 @ X34 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X37 @ X34 ) @ ( sk_D @ X37 @ X34 ) ) @ X34 )
      | ( r2_hidden @ ( sk_C @ X37 @ X34 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k1_tarski @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( m1_subset_1 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('32',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','39'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('41',plain,(
    ! [X41: $i,X44: $i] :
      ( ( X44
        = ( k2_relat_1 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X44 @ X41 ) @ ( sk_C_1 @ X44 @ X41 ) ) @ X41 )
      | ( r2_hidden @ ( sk_C_1 @ X44 @ X41 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X33 ) @ X34 )
      | ( r2_hidden @ X32 @ X35 )
      | ( X35
       != ( k1_relat_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ ( k1_relat_1 @ X34 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X33 ) @ X34 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

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

thf('51',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('54',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('58',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','72'])).

thf('74',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','58'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','58'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 )
      | ( m1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('112',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(condensation,[status(thm)],['114'])).

thf('116',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6yIjDXXrA0
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.17  % Solved by: fo/fo7.sh
% 0.98/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.17  % done 1030 iterations in 0.725s
% 0.98/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.17  % SZS output start Refutation
% 0.98/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.98/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.98/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.98/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.98/1.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.98/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.98/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.17  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.98/1.17  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.98/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.17  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.17  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.17  thf(d4_relat_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.98/1.17       ( ![C:$i]:
% 0.98/1.17         ( ( r2_hidden @ C @ B ) <=>
% 0.98/1.17           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.98/1.17  thf('2', plain,
% 0.98/1.17      (![X34 : $i, X37 : $i]:
% 0.98/1.17         (((X37) = (k1_relat_1 @ X34))
% 0.98/1.17          | (r2_hidden @ 
% 0.98/1.17             (k4_tarski @ (sk_C @ X37 @ X34) @ (sk_D @ X37 @ X34)) @ X34)
% 0.98/1.17          | (r2_hidden @ (sk_C @ X37 @ X34) @ X37))),
% 0.98/1.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.98/1.17  thf(l1_zfmisc_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.98/1.17  thf('3', plain,
% 0.98/1.17      (![X12 : $i, X14 : $i]:
% 0.98/1.17         ((r1_tarski @ (k1_tarski @ X12) @ X14) | ~ (r2_hidden @ X12 @ X14))),
% 0.98/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.98/1.17  thf('4', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.98/1.17          | ((X1) = (k1_relat_1 @ X0))
% 0.98/1.17          | (r1_tarski @ 
% 0.98/1.17             (k1_tarski @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0))) @ 
% 0.98/1.17             X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.98/1.17  thf(t3_xboole_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.98/1.17  thf('5', plain,
% 0.98/1.17      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.98/1.17      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.98/1.17  thf('6', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.98/1.17          | ((k1_tarski @ 
% 0.98/1.17              (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ 
% 0.98/1.17               (sk_D @ X0 @ k1_xboole_0)))
% 0.98/1.17              = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.98/1.17  thf('7', plain,
% 0.98/1.17      (![X12 : $i, X13 : $i]:
% 0.98/1.17         ((r2_hidden @ X12 @ X13) | ~ (r1_tarski @ (k1_tarski @ X12) @ X13))),
% 0.98/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.98/1.17  thf('8', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ 
% 0.98/1.17             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.98/1.17             X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.98/1.17  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.98/1.17  thf('9', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.98/1.17      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.98/1.17  thf('10', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ 
% 0.98/1.17             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.98/1.17             X0))),
% 0.98/1.17      inference('demod', [status(thm)], ['8', '9'])).
% 0.98/1.17  thf(t152_zfmisc_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.98/1.17  thf('11', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('12', plain,
% 0.98/1.17      (![X1 : $i]:
% 0.98/1.17         (((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.17  thf(t4_subset_1, axiom,
% 0.98/1.17    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.98/1.17  thf('13', plain,
% 0.98/1.17      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.98/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.98/1.17  thf(t4_subset, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.98/1.17       ( m1_subset_1 @ A @ C ) ))).
% 0.98/1.17  thf('14', plain,
% 0.98/1.17      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.98/1.17         (~ (r2_hidden @ X29 @ X30)
% 0.98/1.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.98/1.17          | (m1_subset_1 @ X29 @ X31))),
% 0.98/1.17      inference('cnf', [status(esa)], [t4_subset])).
% 0.98/1.17  thf('15', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('16', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['12', '15'])).
% 0.98/1.17  thf(d2_subset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ( v1_xboole_0 @ A ) =>
% 0.98/1.17         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.98/1.17       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.98/1.17         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.17  thf('17', plain,
% 0.98/1.17      (![X24 : $i, X25 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X25 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X25)
% 0.98/1.17          | ~ (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('18', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['16', '17'])).
% 0.98/1.17  thf(t6_boole, axiom,
% 0.98/1.17    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.98/1.17  thf('19', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('20', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.98/1.17  thf('21', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['12', '15'])).
% 0.98/1.17  thf('22', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ k1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['20', '21'])).
% 0.98/1.17  thf('23', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ k1_xboole_0 @ X0))),
% 0.98/1.17      inference('simplify', [status(thm)], ['22'])).
% 0.98/1.17  thf('24', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((m1_subset_1 @ k1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['1', '23'])).
% 0.98/1.17  thf('25', plain,
% 0.98/1.17      (![X23 : $i, X24 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X23 @ X24)
% 0.98/1.17          | (r2_hidden @ X23 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('26', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (v1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['24', '25'])).
% 0.98/1.17  thf('27', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('28', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.17  thf('29', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('30', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['28', '29'])).
% 0.98/1.17  thf('31', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('32', plain,
% 0.98/1.17      ((~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['30', '31'])).
% 0.98/1.17  thf('33', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.17  thf('34', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.98/1.17  thf('35', plain,
% 0.98/1.17      (![X1 : $i]:
% 0.98/1.17         (((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.17  thf('36', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['34', '35'])).
% 0.98/1.17  thf('37', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.98/1.17      inference('simplify', [status(thm)], ['36'])).
% 0.98/1.17  thf('38', plain,
% 0.98/1.17      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17        | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['33', '37'])).
% 0.98/1.17  thf('39', plain,
% 0.98/1.17      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.98/1.17      inference('simplify', [status(thm)], ['38'])).
% 0.98/1.17  thf('40', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.98/1.17      inference('clc', [status(thm)], ['32', '39'])).
% 0.98/1.17  thf(d5_relat_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.98/1.17       ( ![C:$i]:
% 0.98/1.17         ( ( r2_hidden @ C @ B ) <=>
% 0.98/1.17           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.98/1.17  thf('41', plain,
% 0.98/1.17      (![X41 : $i, X44 : $i]:
% 0.98/1.17         (((X44) = (k2_relat_1 @ X41))
% 0.98/1.17          | (r2_hidden @ 
% 0.98/1.17             (k4_tarski @ (sk_D_2 @ X44 @ X41) @ (sk_C_1 @ X44 @ X41)) @ X41)
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ X44 @ X41) @ X44))),
% 0.98/1.17      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.98/1.17  thf('42', plain,
% 0.98/1.17      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.98/1.17         (~ (r2_hidden @ (k4_tarski @ X32 @ X33) @ X34)
% 0.98/1.17          | (r2_hidden @ X32 @ X35)
% 0.98/1.17          | ((X35) != (k1_relat_1 @ X34)))),
% 0.98/1.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.98/1.17  thf('43', plain,
% 0.98/1.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.98/1.17         ((r2_hidden @ X32 @ (k1_relat_1 @ X34))
% 0.98/1.17          | ~ (r2_hidden @ (k4_tarski @ X32 @ X33) @ X34))),
% 0.98/1.17      inference('simplify', [status(thm)], ['42'])).
% 0.98/1.17  thf('44', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.98/1.17          | ((X1) = (k2_relat_1 @ X0))
% 0.98/1.17          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['41', '43'])).
% 0.98/1.17  thf('45', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_D_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.98/1.17          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup+', [status(thm)], ['40', '44'])).
% 0.98/1.17  thf('46', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('47', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.98/1.17          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ (sk_D_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['45', '46'])).
% 0.98/1.17  thf('48', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.98/1.17          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ (sk_D_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['45', '46'])).
% 0.98/1.17  thf('49', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('50', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['48', '49'])).
% 0.98/1.17  thf(t60_relat_1, conjecture,
% 0.98/1.17    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.98/1.17     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.98/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.17    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.98/1.17        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.98/1.17    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.98/1.17  thf('51', plain,
% 0.98/1.17      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.98/1.17        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('52', plain,
% 0.98/1.17      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.98/1.17         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.17      inference('split', [status(esa)], ['51'])).
% 0.98/1.17  thf('53', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.98/1.17      inference('clc', [status(thm)], ['32', '39'])).
% 0.98/1.17  thf('54', plain,
% 0.98/1.17      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.98/1.17         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.17      inference('split', [status(esa)], ['51'])).
% 0.98/1.17  thf('55', plain,
% 0.98/1.17      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.98/1.17         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['53', '54'])).
% 0.98/1.17  thf('56', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('simplify', [status(thm)], ['55'])).
% 0.98/1.17  thf('57', plain,
% 0.98/1.17      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.98/1.17       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('split', [status(esa)], ['51'])).
% 0.98/1.17  thf('58', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.98/1.17  thf('59', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.98/1.17      inference('simpl_trail', [status(thm)], ['52', '58'])).
% 0.98/1.17  thf('60', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['50', '59'])).
% 0.98/1.17  thf('61', plain,
% 0.98/1.17      (![X24 : $i, X25 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X25 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X25)
% 0.98/1.17          | ~ (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('62', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (v1_xboole_0 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.98/1.17  thf('63', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('64', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['62', '63'])).
% 0.98/1.17  thf('65', plain,
% 0.98/1.17      (![X23 : $i, X24 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X23 @ X24)
% 0.98/1.17          | (r2_hidden @ X23 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('66', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | (v1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['64', '65'])).
% 0.98/1.17  thf('67', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('68', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((v1_xboole_0 @ 
% 0.98/1.17           (k2_zfmisc_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['66', '67'])).
% 0.98/1.17  thf('69', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('70', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((k2_zfmisc_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.98/1.17              = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['68', '69'])).
% 0.98/1.17  thf('71', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('72', plain,
% 0.98/1.17      (![X1 : $i]:
% 0.98/1.17         (~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.98/1.17  thf('73', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['47', '72'])).
% 0.98/1.17  thf('74', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.98/1.17      inference('simpl_trail', [status(thm)], ['52', '58'])).
% 0.98/1.17  thf('75', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0) @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.98/1.17  thf('76', plain,
% 0.98/1.17      (![X24 : $i, X25 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X25 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X25)
% 0.98/1.17          | ~ (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('77', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (v1_xboole_0 @ (sk_D_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['75', '76'])).
% 0.98/1.17  thf('78', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('79', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['77', '78'])).
% 0.98/1.17  thf('80', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.17      inference('simplify', [status(thm)], ['79'])).
% 0.98/1.17  thf('81', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((sk_D_2 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('condensation', [status(thm)], ['80'])).
% 0.98/1.17  thf('82', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.98/1.17          | ((X1) = (k2_relat_1 @ X0))
% 0.98/1.17          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['41', '43'])).
% 0.98/1.17  thf('83', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.98/1.17      inference('sup+', [status(thm)], ['81', '82'])).
% 0.98/1.17  thf('84', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.98/1.17      inference('clc', [status(thm)], ['32', '39'])).
% 0.98/1.17  thf('85', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.98/1.17      inference('demod', [status(thm)], ['83', '84'])).
% 0.98/1.17  thf('86', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.98/1.17      inference('simpl_trail', [status(thm)], ['52', '58'])).
% 0.98/1.17  thf('87', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.98/1.17  thf('88', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('89', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X1)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['87', '88'])).
% 0.98/1.17  thf('90', plain,
% 0.98/1.17      (![X24 : $i, X25 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X25 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X25)
% 0.98/1.17          | ~ (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('91', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (v1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['89', '90'])).
% 0.98/1.17  thf('92', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('93', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['91', '92'])).
% 0.98/1.17  thf('94', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.98/1.17  thf('95', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ~ (v1_xboole_0 @ X2)
% 0.98/1.17          | ~ (v1_xboole_0 @ X0)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.98/1.17      inference('sup+', [status(thm)], ['93', '94'])).
% 0.98/1.17  thf('96', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X2)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.98/1.17      inference('simplify', [status(thm)], ['95'])).
% 0.98/1.17  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.17  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.17  thf('99', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X2)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.98/1.17      inference('simplify', [status(thm)], ['95'])).
% 0.98/1.17  thf('100', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('101', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ~ (v1_xboole_0 @ X2)
% 0.98/1.17          | ~ (v1_xboole_0 @ X3)
% 0.98/1.17          | (m1_subset_1 @ k1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['99', '100'])).
% 0.98/1.17  thf('102', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         ((m1_subset_1 @ k1_xboole_0 @ X0)
% 0.98/1.17          | ~ (v1_xboole_0 @ X1)
% 0.98/1.17          | ~ (v1_xboole_0 @ X2))),
% 0.98/1.17      inference('sup-', [status(thm)], ['98', '101'])).
% 0.98/1.17  thf('103', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((m1_subset_1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.17      inference('condensation', [status(thm)], ['102'])).
% 0.98/1.17  thf('104', plain, (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ X0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['97', '103'])).
% 0.98/1.17  thf('105', plain,
% 0.98/1.17      (![X23 : $i, X24 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X23 @ X24)
% 0.98/1.17          | (r2_hidden @ X23 @ X24)
% 0.98/1.17          | (v1_xboole_0 @ X24))),
% 0.98/1.17      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.17  thf('106', plain,
% 0.98/1.17      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ k1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['104', '105'])).
% 0.98/1.17  thf('107', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('108', plain,
% 0.98/1.17      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['106', '107'])).
% 0.98/1.17  thf('109', plain,
% 0.98/1.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t6_boole])).
% 0.98/1.17  thf('110', plain,
% 0.98/1.17      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['108', '109'])).
% 0.98/1.17  thf('111', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.98/1.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.98/1.17  thf('112', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['110', '111'])).
% 0.98/1.17  thf('113', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2))),
% 0.98/1.17      inference('sup-', [status(thm)], ['96', '112'])).
% 0.98/1.17  thf('114', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.17      inference('condensation', [status(thm)], ['113'])).
% 0.98/1.17  thf('115', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.98/1.17      inference('condensation', [status(thm)], ['114'])).
% 0.98/1.17  thf('116', plain, ($false), inference('sup-', [status(thm)], ['0', '115'])).
% 0.98/1.17  
% 0.98/1.17  % SZS output end Refutation
% 0.98/1.17  
% 0.98/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
