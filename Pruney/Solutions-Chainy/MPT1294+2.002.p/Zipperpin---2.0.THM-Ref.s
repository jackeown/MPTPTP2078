%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tk3wLzqyxT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:09 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 288 expanded)
%              Number of leaves         :   21 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  667 (2780 expanded)
%              Number of equality atoms :   93 ( 396 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t10_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) )
        & ~ ( ( ( k7_setfam_1 @ A @ B )
             != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ~ ( ( B != k1_xboole_0 )
              & ( ( k7_setfam_1 @ A @ B )
                = k1_xboole_0 ) )
          & ~ ( ( ( k7_setfam_1 @ A @ B )
               != k1_xboole_0 )
              & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_tops_2])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X14 ) @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_setfam_1 @ X13 @ ( k7_setfam_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_setfam_1 @ X1 @ ( k7_setfam_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_setfam_1 @ X13 @ ( k7_setfam_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('30',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_B_1 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k7_setfam_1 @ sk_A @ X0 )
          = sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 = sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k7_setfam_1 @ sk_A @ X0 ) ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 = sk_B_1 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('46',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( ( k7_setfam_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( ( k7_setfam_1 @ sk_A @ X0 )
         != sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_xboole_0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k7_setfam_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','60'])).

thf('62',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('63',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','61','62'])).

thf('64',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['38','63'])).

thf('65',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','64'])).

thf('66',plain,
    ( $false
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','61'])).

thf('68',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tk3wLzqyxT
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.74/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.96  % Solved by: fo/fo7.sh
% 0.74/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.96  % done 1333 iterations in 0.516s
% 0.74/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.96  % SZS output start Refutation
% 0.74/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.74/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.96  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.74/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.96  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.96  thf(t10_tops_2, conjecture,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.96       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.96              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.96         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.96              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.74/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.96    (~( ![A:$i,B:$i]:
% 0.74/0.96        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.96          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.96                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.96            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.96                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.74/0.96    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.74/0.96  thf('0', plain,
% 0.74/0.96      ((((sk_B_1) != (k1_xboole_0))
% 0.74/0.96        | ((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('1', plain,
% 0.74/0.96      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['0'])).
% 0.74/0.96  thf(d1_xboole_0, axiom,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.96  thf('2', plain,
% 0.74/0.96      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.96      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.96  thf(t4_subset_1, axiom,
% 0.74/0.96    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.74/0.96  thf('3', plain,
% 0.74/0.96      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(dt_k7_setfam_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.96       ( m1_subset_1 @
% 0.74/0.96         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.74/0.96  thf('4', plain,
% 0.74/0.96      (![X10 : $i, X11 : $i]:
% 0.74/0.96         ((m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 0.74/0.96           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.74/0.96          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.74/0.96      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.74/0.96  thf('5', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.74/0.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.96  thf(t49_setfam_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.96       ( ![C:$i]:
% 0.74/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.96           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.74/0.96             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.74/0.96  thf('6', plain,
% 0.74/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.74/0.96          | ~ (r2_hidden @ X14 @ X16)
% 0.74/0.96          | (r2_hidden @ (k3_subset_1 @ X15 @ X14) @ (k7_setfam_1 @ X15 @ X16))
% 0.74/0.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.74/0.96      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.74/0.96  thf('7', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ 
% 0.74/0.96           (k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))
% 0.74/0.96          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.74/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.74/0.96  thf('8', plain,
% 0.74/0.96      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(involutiveness_k7_setfam_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.96       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.74/0.96  thf('9', plain,
% 0.74/0.96      (![X12 : $i, X13 : $i]:
% 0.74/0.96         (((k7_setfam_1 @ X13 @ (k7_setfam_1 @ X13 @ X12)) = (X12))
% 0.74/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.74/0.96      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.74/0.96  thf('10', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.96  thf('11', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.74/0.96          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.74/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.74/0.96      inference('demod', [status(thm)], ['7', '10'])).
% 0.74/0.96  thf(t113_zfmisc_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]:
% 0.74/0.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.74/0.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.74/0.96  thf('12', plain,
% 0.74/0.96      (![X5 : $i, X6 : $i]:
% 0.74/0.96         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.96  thf('13', plain,
% 0.74/0.96      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.96      inference('simplify', [status(thm)], ['12'])).
% 0.74/0.96  thf(t152_zfmisc_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.74/0.96  thf('14', plain,
% 0.74/0.96      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.74/0.96      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.74/0.96  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/0.96  thf('16', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.74/0.96          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.74/0.96      inference('clc', [status(thm)], ['11', '15'])).
% 0.74/0.96  thf('17', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.74/0.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.96  thf(t4_subset, axiom,
% 0.74/0.96    (![A:$i,B:$i,C:$i]:
% 0.74/0.96     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.74/0.96       ( m1_subset_1 @ A @ C ) ))).
% 0.74/0.96  thf('18', plain,
% 0.74/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.74/0.96         (~ (r2_hidden @ X17 @ X18)
% 0.74/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.74/0.96          | (m1_subset_1 @ X17 @ X19))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset])).
% 0.74/0.96  thf('19', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.74/0.96          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.74/0.96  thf('20', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.74/0.96      inference('clc', [status(thm)], ['16', '19'])).
% 0.74/0.96  thf('21', plain,
% 0.74/0.96      (![X0 : $i]: (v1_xboole_0 @ (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['2', '20'])).
% 0.74/0.96  thf(l13_xboole_0, axiom,
% 0.74/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.96  thf('22', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('23', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.96  thf('24', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         (((k7_setfam_1 @ X1 @ (k7_setfam_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.74/0.96          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('sup+', [status(thm)], ['22', '23'])).
% 0.74/0.96  thf('25', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('26', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('27', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('28', plain,
% 0.74/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('29', plain,
% 0.74/0.96      (![X12 : $i, X13 : $i]:
% 0.74/0.96         (((k7_setfam_1 @ X13 @ (k7_setfam_1 @ X13 @ X12)) = (X12))
% 0.74/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.74/0.96      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.74/0.96  thf('30', plain,
% 0.74/0.96      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.74/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.74/0.96  thf('31', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1)))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['27', '30'])).
% 0.74/0.96  thf('32', plain,
% 0.74/0.96      ((![X0 : $i]:
% 0.74/0.96          (((k7_setfam_1 @ sk_A @ X0) = (sk_B_1)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['25', '31'])).
% 0.74/0.96  thf('33', plain,
% 0.74/0.96      ((![X0 : $i]:
% 0.74/0.96          (((k1_xboole_0) = (sk_B_1))
% 0.74/0.96           | ~ (v1_xboole_0 @ X0)
% 0.74/0.96           | ~ (v1_xboole_0 @ (k7_setfam_1 @ sk_A @ X0))))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['24', '32'])).
% 0.74/0.96  thf('34', plain,
% 0.74/0.96      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_B_1))))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['21', '33'])).
% 0.74/0.96  thf('35', plain,
% 0.74/0.96      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.96      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.96  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/0.96  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.96  thf('38', plain,
% 0.74/0.96      ((((k1_xboole_0) = (sk_B_1)))
% 0.74/0.96         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('demod', [status(thm)], ['34', '37'])).
% 0.74/0.96  thf('39', plain,
% 0.74/0.96      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.74/0.96       ~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('split', [status(esa)], ['0'])).
% 0.74/0.96  thf('40', plain,
% 0.74/0.96      (![X0 : $i]: (v1_xboole_0 @ (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['2', '20'])).
% 0.74/0.96  thf('41', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('42', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('43', plain,
% 0.74/0.96      ((![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['41', '42'])).
% 0.74/0.96  thf('44', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.96  thf('45', plain,
% 0.74/0.96      ((![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['41', '42'])).
% 0.74/0.96  thf('46', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['0'])).
% 0.74/0.96  thf('47', plain,
% 0.74/0.96      ((![X0 : $i]:
% 0.74/0.96          (((k7_setfam_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.96  thf('48', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('49', plain,
% 0.74/0.96      ((![X0 : $i]:
% 0.74/0.96          (((k7_setfam_1 @ sk_A @ X0) != (sk_B_1)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('demod', [status(thm)], ['47', '48'])).
% 0.74/0.96  thf('50', plain,
% 0.74/0.96      (((((k1_xboole_0) != (sk_B_1))
% 0.74/0.96         | ~ (v1_xboole_0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['44', '49'])).
% 0.74/0.96  thf('51', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('52', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('53', plain,
% 0.74/0.96      (((((sk_B_1) != (sk_B_1))
% 0.74/0.96         | ~ (v1_xboole_0 @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.74/0.96  thf('54', plain,
% 0.74/0.96      ((~ (v1_xboole_0 @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('simplify', [status(thm)], ['53'])).
% 0.74/0.96  thf('55', plain,
% 0.74/0.96      ((![X0 : $i]:
% 0.74/0.96          (~ (v1_xboole_0 @ (k7_setfam_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['43', '54'])).
% 0.74/0.96  thf('56', plain,
% 0.74/0.96      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.74/0.96         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.96             (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['40', '55'])).
% 0.74/0.96  thf('57', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('58', plain,
% 0.74/0.96      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.96  thf('60', plain,
% 0.74/0.96      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('sup+', [status(thm)], ['58', '59'])).
% 0.74/0.96  thf('61', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.74/0.96       ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('demod', [status(thm)], ['56', '57', '60'])).
% 0.74/0.96  thf('62', plain,
% 0.74/0.96      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.74/0.96       (((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('split', [status(esa)], ['26'])).
% 0.74/0.96  thf('63', plain, ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('sat_resolution*', [status(thm)], ['39', '61', '62'])).
% 0.74/0.96  thf('64', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.74/0.96      inference('simpl_trail', [status(thm)], ['38', '63'])).
% 0.74/0.96  thf('65', plain,
% 0.74/0.96      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('demod', [status(thm)], ['1', '64'])).
% 0.74/0.96  thf('66', plain, (($false) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.96      inference('simplify', [status(thm)], ['65'])).
% 0.74/0.96  thf('67', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('sat_resolution*', [status(thm)], ['39', '61'])).
% 0.74/0.96  thf('68', plain, ($false),
% 0.74/0.96      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.74/0.96  
% 0.74/0.96  % SZS output end Refutation
% 0.74/0.96  
% 0.74/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
