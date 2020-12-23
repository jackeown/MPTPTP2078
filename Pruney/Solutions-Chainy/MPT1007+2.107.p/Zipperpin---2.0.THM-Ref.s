%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1j4aqRu5jF

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 211 expanded)
%              Number of leaves         :   41 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  599 (2100 expanded)
%              Number of equality atoms :   43 ( 124 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X38 @ X35 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_mcart_1 @ X27 )
        = X26 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ ( k1_tarski @ X26 ) @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('29',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('33',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','31','34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','24','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','44'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','45'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('52',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['50','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1j4aqRu5jF
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 115 iterations in 0.053s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(t6_mcart_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.50                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.50                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.19/0.50                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.19/0.50                       ( r2_hidden @ G @ B ) ) =>
% 0.19/0.50                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X29 : $i]:
% 0.19/0.50         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X29) @ X29))),
% 0.19/0.50      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.19/0.50  thf(t61_funct_2, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.50         ( m1_subset_1 @
% 0.19/0.50           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.50         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.50            ( m1_subset_1 @
% 0.19/0.50              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.50            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t7_funct_2, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50       ( ( r2_hidden @ C @ A ) =>
% 0.19/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X35 @ X36)
% 0.19/0.50          | ((X37) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_funct_1 @ X38)
% 0.19/0.50          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.19/0.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.19/0.50          | (r2_hidden @ (k1_funct_1 @ X38 @ X35) @ X37))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.50          | ((sk_B_2) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.19/0.50          | ((sk_B_2) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.50  thf('7', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X29 : $i]:
% 0.19/0.50         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X29) @ X29))),
% 0.19/0.50      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(l3_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X10 @ X11)
% 0.19/0.50          | (r2_hidden @ X10 @ X12)
% 0.19/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.19/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.50  thf(t12_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.19/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.19/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.50         (((k1_mcart_1 @ X27) = (X26))
% 0.19/0.50          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ (k1_tarski @ X26) @ X28)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B_1 @ sk_C)) = (sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.19/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.50  thf(t10_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_mcart_1 @ X23) @ X24)
% 0.19/0.50          | ~ (r2_hidden @ X23 @ (k2_zfmisc_1 @ X24 @ X25)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.19/0.50        | ((sk_C) = (k1_xboole_0))
% 0.19/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['15', '18'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.50      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf(t60_relat_1, axiom,
% 0.19/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.50  thf(d4_funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.50       ( ![B:$i,C:$i]:
% 0.19/0.50         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.19/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.50               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.50           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.50               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.19/0.50          | ((X17) = (k1_xboole_0))
% 0.19/0.50          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.19/0.50          | ~ (v1_funct_1 @ X16)
% 0.19/0.50          | ~ (v1_relat_1 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X16)
% 0.19/0.50          | ~ (v1_funct_1 @ X16)
% 0.19/0.50          | ((k1_funct_1 @ X16 @ X15) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['25', '27'])).
% 0.19/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.50  thf('29', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.50  thf(fc3_funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.50  thf('30', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('31', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.50  thf('33', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['28', '31', '34'])).
% 0.19/0.50  thf(t7_ordinal1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.19/0.50          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.50  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '24', '39'])).
% 0.19/0.50  thf('41', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('42', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.50      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('44', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.19/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.19/0.50  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['40', '44'])).
% 0.19/0.50  thf('46', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '45'])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('47', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(fc3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.19/0.50  thf('49', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '49'])).
% 0.19/0.50  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.50  thf(existence_m1_subset_1, axiom,
% 0.19/0.50    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.19/0.50  thf('52', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.19/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.19/0.50  thf(t2_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((r2_hidden @ X13 @ X14)
% 0.19/0.50          | (v1_xboole_0 @ X14)
% 0.19/0.50          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.50  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['51', '56'])).
% 0.19/0.50  thf('58', plain, ($false), inference('demod', [status(thm)], ['50', '57'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
