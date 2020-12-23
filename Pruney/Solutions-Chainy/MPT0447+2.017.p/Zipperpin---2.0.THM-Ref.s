%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jD6famMITr

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 483 expanded)
%              Number of leaves         :   30 ( 154 expanded)
%              Depth                    :   25
%              Number of atoms          : 1124 (4020 expanded)
%              Number of equality atoms :   41 ( 185 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ X42 ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','34'])).

thf('36',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_relat_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ X42 ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('53',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['51','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('59',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36
        = ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X36 @ X33 ) @ ( sk_D_1 @ X36 @ X33 ) ) @ X33 )
      | ( r2_hidden @ ( sk_C_1 @ X36 @ X33 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('65',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('67',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('72',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','74','81'])).

thf('83',plain,(
    r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','82'])).

thf('84',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('96',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k3_relat_1 @ k1_xboole_0 ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('98',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k3_relat_1 @ k1_xboole_0 ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('101',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k3_relat_1 @ sk_B ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['98','107'])).

thf('109',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('118',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('120',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ X42 ) @ ( k1_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','128'])).

thf('130',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('131',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('135',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jD6famMITr
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.66/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.88  % Solved by: fo/fo7.sh
% 1.66/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.88  % done 3479 iterations in 1.417s
% 1.66/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.88  % SZS output start Refutation
% 1.66/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.66/1.88  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.66/1.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.66/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.66/1.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.66/1.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.66/1.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.66/1.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.88  thf(t31_relat_1, conjecture,
% 1.66/1.88    (![A:$i]:
% 1.66/1.88     ( ( v1_relat_1 @ A ) =>
% 1.66/1.88       ( ![B:$i]:
% 1.66/1.88         ( ( v1_relat_1 @ B ) =>
% 1.66/1.88           ( ( r1_tarski @ A @ B ) =>
% 1.66/1.88             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.66/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.88    (~( ![A:$i]:
% 1.66/1.88        ( ( v1_relat_1 @ A ) =>
% 1.66/1.88          ( ![B:$i]:
% 1.66/1.88            ( ( v1_relat_1 @ B ) =>
% 1.66/1.88              ( ( r1_tarski @ A @ B ) =>
% 1.66/1.88                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.66/1.88    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.66/1.88  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf(d6_relat_1, axiom,
% 1.66/1.88    (![A:$i]:
% 1.66/1.88     ( ( v1_relat_1 @ A ) =>
% 1.66/1.88       ( ( k3_relat_1 @ A ) =
% 1.66/1.88         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.66/1.88  thf('1', plain,
% 1.66/1.88      (![X38 : $i]:
% 1.66/1.88         (((k3_relat_1 @ X38)
% 1.66/1.88            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 1.66/1.88          | ~ (v1_relat_1 @ X38))),
% 1.66/1.88      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.66/1.88  thf('2', plain,
% 1.66/1.88      (![X38 : $i]:
% 1.66/1.88         (((k3_relat_1 @ X38)
% 1.66/1.88            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 1.66/1.88          | ~ (v1_relat_1 @ X38))),
% 1.66/1.88      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.66/1.88  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf(t25_relat_1, axiom,
% 1.66/1.88    (![A:$i]:
% 1.66/1.88     ( ( v1_relat_1 @ A ) =>
% 1.66/1.88       ( ![B:$i]:
% 1.66/1.88         ( ( v1_relat_1 @ B ) =>
% 1.66/1.88           ( ( r1_tarski @ A @ B ) =>
% 1.66/1.88             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.66/1.88               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.66/1.88  thf('4', plain,
% 1.66/1.88      (![X41 : $i, X42 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ X41)
% 1.66/1.88          | (r1_tarski @ (k2_relat_1 @ X42) @ (k2_relat_1 @ X41))
% 1.66/1.88          | ~ (r1_tarski @ X42 @ X41)
% 1.66/1.88          | ~ (v1_relat_1 @ X42))),
% 1.66/1.88      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.66/1.88  thf('5', plain,
% 1.66/1.88      ((~ (v1_relat_1 @ sk_A)
% 1.66/1.88        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.66/1.88        | ~ (v1_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['3', '4'])).
% 1.66/1.88  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.66/1.88  thf(t10_xboole_1, axiom,
% 1.66/1.88    (![A:$i,B:$i,C:$i]:
% 1.66/1.88     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.66/1.88  thf('9', plain,
% 1.66/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X13 @ X14)
% 1.66/1.88          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.66/1.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.88  thf('10', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.66/1.88          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['8', '9'])).
% 1.66/1.88  thf('11', plain,
% 1.66/1.88      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.66/1.88        | ~ (v1_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup+', [status(thm)], ['2', '10'])).
% 1.66/1.88  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['11', '12'])).
% 1.66/1.88  thf(d10_xboole_0, axiom,
% 1.66/1.88    (![A:$i,B:$i]:
% 1.66/1.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.66/1.88  thf('14', plain,
% 1.66/1.88      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.66/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.88  thf('15', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.66/1.88      inference('simplify', [status(thm)], ['14'])).
% 1.66/1.88  thf(t8_xboole_1, axiom,
% 1.66/1.88    (![A:$i,B:$i,C:$i]:
% 1.66/1.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.66/1.88       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.66/1.88  thf('16', plain,
% 1.66/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X21 @ X22)
% 1.66/1.88          | ~ (r1_tarski @ X23 @ X22)
% 1.66/1.88          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 1.66/1.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.88  thf('17', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['15', '16'])).
% 1.66/1.88  thf('18', plain,
% 1.66/1.88      ((r1_tarski @ 
% 1.66/1.88        (k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.88        (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['13', '17'])).
% 1.66/1.88  thf(d5_xboole_0, axiom,
% 1.66/1.88    (![A:$i,B:$i,C:$i]:
% 1.66/1.88     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.66/1.88       ( ![D:$i]:
% 1.66/1.88         ( ( r2_hidden @ D @ C ) <=>
% 1.66/1.88           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.66/1.88  thf('19', plain,
% 1.66/1.88      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.66/1.88         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 1.66/1.88          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.66/1.88          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.66/1.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.66/1.88  thf('20', plain,
% 1.66/1.88      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.66/1.88         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 1.66/1.88          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.66/1.88          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.66/1.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.66/1.88  thf('21', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.66/1.88          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.66/1.88          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.66/1.88          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['19', '20'])).
% 1.66/1.88  thf('22', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.66/1.88          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.66/1.88      inference('simplify', [status(thm)], ['21'])).
% 1.66/1.88  thf(t3_boole, axiom,
% 1.66/1.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.66/1.88  thf('23', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.66/1.88      inference('cnf', [status(esa)], [t3_boole])).
% 1.66/1.88  thf('24', plain,
% 1.66/1.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.66/1.88         (~ (r2_hidden @ X8 @ X7)
% 1.66/1.88          | ~ (r2_hidden @ X8 @ X6)
% 1.66/1.88          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.66/1.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.66/1.88  thf('25', plain,
% 1.66/1.88      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.66/1.88         (~ (r2_hidden @ X8 @ X6)
% 1.66/1.88          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.66/1.88      inference('simplify', [status(thm)], ['24'])).
% 1.66/1.88  thf('26', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['23', '25'])).
% 1.66/1.88  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.66/1.88      inference('condensation', [status(thm)], ['26'])).
% 1.66/1.88  thf('28', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['22', '27'])).
% 1.66/1.88  thf(t44_xboole_1, axiom,
% 1.66/1.88    (![A:$i,B:$i,C:$i]:
% 1.66/1.88     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.66/1.88       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.66/1.88  thf('29', plain,
% 1.66/1.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.88         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.66/1.88          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 1.66/1.88      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.66/1.88  thf('30', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.66/1.88          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['28', '29'])).
% 1.66/1.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.66/1.88  thf('31', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.66/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.66/1.88  thf('32', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.88  thf('33', plain,
% 1.66/1.88      (![X10 : $i, X12 : $i]:
% 1.66/1.88         (((X10) = (X12))
% 1.66/1.88          | ~ (r1_tarski @ X12 @ X10)
% 1.66/1.88          | ~ (r1_tarski @ X10 @ X12))),
% 1.66/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.88  thf('34', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.66/1.88          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['32', '33'])).
% 1.66/1.88  thf('35', plain,
% 1.66/1.88      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A))
% 1.66/1.88         = (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['18', '34'])).
% 1.66/1.88  thf('36', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.66/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.66/1.88  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('38', plain,
% 1.66/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X21 @ X22)
% 1.66/1.88          | ~ (r1_tarski @ X23 @ X22)
% 1.66/1.88          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 1.66/1.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.88  thf('39', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.66/1.88          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['37', '38'])).
% 1.66/1.88  thf('40', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)),
% 1.66/1.88      inference('sup-', [status(thm)], ['36', '39'])).
% 1.66/1.88  thf(t3_subset, axiom,
% 1.66/1.88    (![A:$i,B:$i]:
% 1.66/1.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.66/1.88  thf('41', plain,
% 1.66/1.88      (![X26 : $i, X28 : $i]:
% 1.66/1.88         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.66/1.88      inference('cnf', [status(esa)], [t3_subset])).
% 1.66/1.88  thf('42', plain,
% 1.66/1.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0) @ (k1_zfmisc_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['40', '41'])).
% 1.66/1.88  thf(cc2_relat_1, axiom,
% 1.66/1.88    (![A:$i]:
% 1.66/1.88     ( ( v1_relat_1 @ A ) =>
% 1.66/1.88       ( ![B:$i]:
% 1.66/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.66/1.88  thf('43', plain,
% 1.66/1.88      (![X29 : $i, X30 : $i]:
% 1.66/1.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.66/1.88          | (v1_relat_1 @ X29)
% 1.66/1.88          | ~ (v1_relat_1 @ X30))),
% 1.66/1.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.88  thf('44', plain,
% 1.66/1.88      ((~ (v1_relat_1 @ sk_B)
% 1.66/1.88        | (v1_relat_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['42', '43'])).
% 1.66/1.88  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('46', plain, ((v1_relat_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.66/1.88      inference('demod', [status(thm)], ['44', '45'])).
% 1.66/1.88  thf('47', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.66/1.88      inference('simplify', [status(thm)], ['14'])).
% 1.66/1.88  thf('48', plain,
% 1.66/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X13 @ X14)
% 1.66/1.88          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.66/1.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.88  thf('49', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['47', '48'])).
% 1.66/1.88  thf('50', plain,
% 1.66/1.88      (![X41 : $i, X42 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ X41)
% 1.66/1.88          | (r1_tarski @ (k2_relat_1 @ X42) @ (k2_relat_1 @ X41))
% 1.66/1.88          | ~ (r1_tarski @ X42 @ X41)
% 1.66/1.88          | ~ (v1_relat_1 @ X42))),
% 1.66/1.88      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.66/1.88  thf('51', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ X0)
% 1.66/1.88          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.66/1.88             (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.66/1.88          | ~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['49', '50'])).
% 1.66/1.88  thf('52', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['47', '48'])).
% 1.66/1.88  thf('53', plain,
% 1.66/1.88      (![X26 : $i, X28 : $i]:
% 1.66/1.88         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.66/1.88      inference('cnf', [status(esa)], [t3_subset])).
% 1.66/1.88  thf('54', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.88  thf('55', plain,
% 1.66/1.88      (![X29 : $i, X30 : $i]:
% 1.66/1.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.66/1.88          | (v1_relat_1 @ X29)
% 1.66/1.88          | ~ (v1_relat_1 @ X30))),
% 1.66/1.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.88  thf('56', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['54', '55'])).
% 1.66/1.88  thf('57', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0))
% 1.66/1.88          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.66/1.88             (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.66/1.88      inference('clc', [status(thm)], ['51', '56'])).
% 1.66/1.88  thf('58', plain,
% 1.66/1.88      ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 1.66/1.88        (k2_relat_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['46', '57'])).
% 1.66/1.88  thf(d4_relat_1, axiom,
% 1.66/1.88    (![A:$i,B:$i]:
% 1.66/1.88     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.66/1.88       ( ![C:$i]:
% 1.66/1.88         ( ( r2_hidden @ C @ B ) <=>
% 1.66/1.88           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.66/1.88  thf('59', plain,
% 1.66/1.88      (![X33 : $i, X36 : $i]:
% 1.66/1.88         (((X36) = (k1_relat_1 @ X33))
% 1.66/1.88          | (r2_hidden @ 
% 1.66/1.88             (k4_tarski @ (sk_C_1 @ X36 @ X33) @ (sk_D_1 @ X36 @ X33)) @ X33)
% 1.66/1.88          | (r2_hidden @ (sk_C_1 @ X36 @ X33) @ X36))),
% 1.66/1.88      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.66/1.88  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.66/1.88      inference('condensation', [status(thm)], ['26'])).
% 1.66/1.88  thf('61', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.66/1.88          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['59', '60'])).
% 1.66/1.88  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.66/1.88      inference('condensation', [status(thm)], ['26'])).
% 1.66/1.88  thf('63', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['61', '62'])).
% 1.66/1.88  thf('64', plain,
% 1.66/1.88      (![X38 : $i]:
% 1.66/1.88         (((k3_relat_1 @ X38)
% 1.66/1.88            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 1.66/1.88          | ~ (v1_relat_1 @ X38))),
% 1.66/1.88      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.66/1.88  thf('65', plain,
% 1.66/1.88      ((((k3_relat_1 @ k1_xboole_0)
% 1.66/1.88          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 1.66/1.88        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.66/1.88      inference('sup+', [status(thm)], ['63', '64'])).
% 1.66/1.88  thf('66', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.66/1.88      inference('simplify', [status(thm)], ['14'])).
% 1.66/1.88  thf('67', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.66/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.66/1.88  thf('68', plain,
% 1.66/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X21 @ X22)
% 1.66/1.88          | ~ (r1_tarski @ X23 @ X22)
% 1.66/1.88          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 1.66/1.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.88  thf('69', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 1.66/1.88          | ~ (r1_tarski @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['67', '68'])).
% 1.66/1.88  thf('70', plain,
% 1.66/1.88      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 1.66/1.88      inference('sup-', [status(thm)], ['66', '69'])).
% 1.66/1.88  thf('71', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['47', '48'])).
% 1.66/1.88  thf('72', plain,
% 1.66/1.88      (![X10 : $i, X12 : $i]:
% 1.66/1.88         (((X10) = (X12))
% 1.66/1.88          | ~ (r1_tarski @ X12 @ X10)
% 1.66/1.88          | ~ (r1_tarski @ X10 @ X12))),
% 1.66/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.88  thf('73', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.66/1.88          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['71', '72'])).
% 1.66/1.88  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['70', '73'])).
% 1.66/1.88  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('76', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.66/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.66/1.88  thf('77', plain,
% 1.66/1.88      (![X26 : $i, X28 : $i]:
% 1.66/1.88         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.66/1.88      inference('cnf', [status(esa)], [t3_subset])).
% 1.66/1.88  thf('78', plain,
% 1.66/1.88      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['76', '77'])).
% 1.66/1.88  thf('79', plain,
% 1.66/1.88      (![X29 : $i, X30 : $i]:
% 1.66/1.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.66/1.88          | (v1_relat_1 @ X29)
% 1.66/1.88          | ~ (v1_relat_1 @ X30))),
% 1.66/1.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.88  thf('80', plain,
% 1.66/1.88      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['78', '79'])).
% 1.66/1.88  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.66/1.88      inference('sup-', [status(thm)], ['75', '80'])).
% 1.66/1.88  thf('82', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 1.66/1.88      inference('demod', [status(thm)], ['65', '74', '81'])).
% 1.66/1.88  thf('83', plain,
% 1.66/1.88      ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ 
% 1.66/1.88        (k2_relat_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0)))),
% 1.66/1.88      inference('demod', [status(thm)], ['58', '82'])).
% 1.66/1.88  thf('84', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.66/1.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.66/1.88  thf('85', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['15', '16'])).
% 1.66/1.88  thf('86', plain,
% 1.66/1.88      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 1.66/1.88      inference('sup-', [status(thm)], ['84', '85'])).
% 1.66/1.88  thf('87', plain,
% 1.66/1.88      (![X10 : $i, X12 : $i]:
% 1.66/1.88         (((X10) = (X12))
% 1.66/1.88          | ~ (r1_tarski @ X12 @ X10)
% 1.66/1.88          | ~ (r1_tarski @ X10 @ X12))),
% 1.66/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.88  thf('88', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 1.66/1.88          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['86', '87'])).
% 1.66/1.88  thf('89', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.88  thf('90', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.66/1.88      inference('demod', [status(thm)], ['88', '89'])).
% 1.66/1.88  thf('91', plain,
% 1.66/1.88      ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ sk_A))),
% 1.66/1.88      inference('demod', [status(thm)], ['83', '90'])).
% 1.66/1.88  thf('92', plain,
% 1.66/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X13 @ X14)
% 1.66/1.88          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.66/1.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.88  thf('93', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         (r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ 
% 1.66/1.88          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_A)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['91', '92'])).
% 1.66/1.88  thf('94', plain,
% 1.66/1.88      ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup+', [status(thm)], ['35', '93'])).
% 1.66/1.88  thf('95', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['15', '16'])).
% 1.66/1.88  thf('96', plain,
% 1.66/1.88      ((r1_tarski @ 
% 1.66/1.88        (k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k3_relat_1 @ k1_xboole_0)) @ 
% 1.66/1.88        (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['94', '95'])).
% 1.66/1.88  thf('97', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.66/1.88          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['32', '33'])).
% 1.66/1.88  thf('98', plain,
% 1.66/1.88      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k3_relat_1 @ k1_xboole_0))
% 1.66/1.88         = (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['96', '97'])).
% 1.66/1.88  thf('99', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.88  thf('100', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['47', '48'])).
% 1.66/1.88  thf('101', plain,
% 1.66/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X21 @ X22)
% 1.66/1.88          | ~ (r1_tarski @ X23 @ X22)
% 1.66/1.88          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 1.66/1.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.88  thf('102', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 1.66/1.88          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['100', '101'])).
% 1.66/1.88  thf('103', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['99', '102'])).
% 1.66/1.88  thf('104', plain,
% 1.66/1.88      (![X10 : $i, X12 : $i]:
% 1.66/1.88         (((X10) = (X12))
% 1.66/1.88          | ~ (r1_tarski @ X12 @ X10)
% 1.66/1.88          | ~ (r1_tarski @ X10 @ X12))),
% 1.66/1.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.88  thf('105', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.66/1.88          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['103', '104'])).
% 1.66/1.88  thf('106', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['99', '102'])).
% 1.66/1.88  thf('107', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.88      inference('demod', [status(thm)], ['105', '106'])).
% 1.66/1.88  thf('108', plain,
% 1.66/1.88      (((k2_xboole_0 @ (k3_relat_1 @ k1_xboole_0) @ (k3_relat_1 @ sk_B))
% 1.66/1.88         = (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['98', '107'])).
% 1.66/1.88  thf('109', plain,
% 1.66/1.88      (![X38 : $i]:
% 1.66/1.88         (((k3_relat_1 @ X38)
% 1.66/1.88            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 1.66/1.88          | ~ (v1_relat_1 @ X38))),
% 1.66/1.88      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.66/1.88  thf('110', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.66/1.88      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.88  thf('111', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.66/1.88          | ~ (v1_relat_1 @ X0))),
% 1.66/1.88      inference('sup+', [status(thm)], ['109', '110'])).
% 1.66/1.88  thf('112', plain,
% 1.66/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X13 @ X14)
% 1.66/1.88          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.66/1.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.88  thf('113', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ X0)
% 1.66/1.88          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.66/1.88             (k2_xboole_0 @ X1 @ (k3_relat_1 @ X0))))),
% 1.66/1.88      inference('sup-', [status(thm)], ['111', '112'])).
% 1.66/1.88  thf('114', plain,
% 1.66/1.88      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))
% 1.66/1.88        | ~ (v1_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup+', [status(thm)], ['108', '113'])).
% 1.66/1.88  thf('115', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('116', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['114', '115'])).
% 1.66/1.88  thf('117', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.66/1.88      inference('sup-', [status(thm)], ['15', '16'])).
% 1.66/1.88  thf('118', plain,
% 1.66/1.88      ((r1_tarski @ 
% 1.66/1.88        (k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)) @ 
% 1.66/1.88        (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['116', '117'])).
% 1.66/1.88  thf('119', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]:
% 1.66/1.88         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.66/1.88          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['32', '33'])).
% 1.66/1.88  thf('120', plain,
% 1.66/1.88      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.66/1.88         = (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['118', '119'])).
% 1.66/1.88  thf('121', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('122', plain,
% 1.66/1.88      (![X41 : $i, X42 : $i]:
% 1.66/1.88         (~ (v1_relat_1 @ X41)
% 1.66/1.88          | (r1_tarski @ (k1_relat_1 @ X42) @ (k1_relat_1 @ X41))
% 1.66/1.88          | ~ (r1_tarski @ X42 @ X41)
% 1.66/1.88          | ~ (v1_relat_1 @ X42))),
% 1.66/1.88      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.66/1.88  thf('123', plain,
% 1.66/1.88      ((~ (v1_relat_1 @ sk_A)
% 1.66/1.88        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.66/1.88        | ~ (v1_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['121', '122'])).
% 1.66/1.88  thf('124', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('125', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('126', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.66/1.88  thf('127', plain,
% 1.66/1.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X13 @ X14)
% 1.66/1.88          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.66/1.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.88  thf('128', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 1.66/1.88          (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['126', '127'])).
% 1.66/1.88  thf('129', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup+', [status(thm)], ['120', '128'])).
% 1.66/1.88  thf('130', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['11', '12'])).
% 1.66/1.88  thf('131', plain,
% 1.66/1.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.66/1.88         (~ (r1_tarski @ X21 @ X22)
% 1.66/1.88          | ~ (r1_tarski @ X23 @ X22)
% 1.66/1.88          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 1.66/1.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.66/1.88  thf('132', plain,
% 1.66/1.88      (![X0 : $i]:
% 1.66/1.88         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 1.66/1.88           (k3_relat_1 @ sk_B))
% 1.66/1.88          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.66/1.88      inference('sup-', [status(thm)], ['130', '131'])).
% 1.66/1.88  thf('133', plain,
% 1.66/1.88      ((r1_tarski @ 
% 1.66/1.88        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 1.66/1.88        (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('sup-', [status(thm)], ['129', '132'])).
% 1.66/1.88  thf('134', plain,
% 1.66/1.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.88      inference('demod', [status(thm)], ['105', '106'])).
% 1.66/1.88  thf('135', plain,
% 1.66/1.88      ((r1_tarski @ 
% 1.66/1.88        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.88        (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['133', '134'])).
% 1.66/1.88  thf('136', plain,
% 1.66/1.88      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.66/1.88        | ~ (v1_relat_1 @ sk_A))),
% 1.66/1.88      inference('sup+', [status(thm)], ['1', '135'])).
% 1.66/1.88  thf('137', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.88  thf('138', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.66/1.88      inference('demod', [status(thm)], ['136', '137'])).
% 1.66/1.88  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 1.66/1.88  
% 1.66/1.88  % SZS output end Refutation
% 1.66/1.88  
% 1.66/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
