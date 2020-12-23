%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S80Iuavxfd

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:39 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 741 expanded)
%              Number of leaves         :   29 ( 216 expanded)
%              Depth                    :   34
%              Number of atoms          : 1411 (9279 expanded)
%              Number of equality atoms :  132 ( 788 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t49_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
            & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
            & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t49_mcart_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X3 @ X4 @ X5 @ X6 ) @ X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X30
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k6_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k7_mcart_1 @ X27 @ X28 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X27 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('25',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( ( sk_B @ X13 )
       != ( k3_mcart_1 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( sk_B @ sk_A ) )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_C = k1_xboole_0 )
        | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X19 @ X20 @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X19 @ X20 @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('42',plain,(
    ! [X19: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X19 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('50',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('56',plain,
    ( ( ( r1_tarski @ sk_A @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('57',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X19: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ X19 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('62',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','60','61'])).

thf('63',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','66','67'])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','68'])).

thf('70',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('71',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X7 @ X8 @ X9 @ X10 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','66','67'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['50'])).

thf('86',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('88',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X30
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k6_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k7_mcart_1 @ X27 @ X28 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X27 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('89',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k7_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k7_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','66','67'])).

thf('93',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ ( k7_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( ( sk_B @ X13 )
       != ( k3_mcart_1 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_B @ sk_A ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_C @ sk_A @ sk_B_1 @ ( sk_B @ sk_A ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','95'])).

thf('97',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','68'])).

thf('101',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ k1_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X19 @ X20 @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('103',plain,(
    ! [X20: $i,X22: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X20 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('106',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('110',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['69','108','109'])).

thf('111',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).


%------------------------------------------------------------------------------
