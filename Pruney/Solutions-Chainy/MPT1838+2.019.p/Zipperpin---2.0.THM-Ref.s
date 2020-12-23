%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDnC2iSygg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:17 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  159 (1345 expanded)
%              Number of leaves         :   31 ( 386 expanded)
%              Depth                    :   33
%              Number of atoms          : 1079 (11942 expanded)
%              Number of equality atoms :  120 (1170 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('8',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_1 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = ( k3_tarski @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = ( k3_tarski @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = ( k3_tarski @ sk_B_2 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ sk_B_2 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B_2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('39',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X13 ) )
      | ( ( sk_C_1 @ X17 @ X13 )
        = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('59',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) )
    = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_B_2
      = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['62','65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_B_2
    = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( X0
        = ( k3_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = ( k3_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('75',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( k3_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( k3_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( sk_B @ sk_A )
      = ( k3_tarski @ sk_B_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('85',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','93'])).

thf('95',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ sk_A )
    | ( sk_B_2 = sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ~ ( r1_tarski @ sk_B_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['96','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != sk_A ) ),
    inference(demod,[status(thm)],['73','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = ( k3_tarski @ sk_B_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','105'])).

thf('107',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X13 ) )
      | ( ( sk_C_1 @ X17 @ X13 )
        = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_A )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,
    ( sk_B_2
    = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( r1_tarski @ sk_B_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != sk_A ) ),
    inference(demod,[status(thm)],['73','104'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( r1_tarski @ sk_B_2 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( r1_tarski @ sk_B_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ sk_A @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X13 ) )
      | ( ( sk_C_1 @ X17 @ X13 )
       != X13 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_A @ X0 )
       != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ sk_A @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != sk_A ) ),
    inference(demod,[status(thm)],['73','104'])).

thf('124',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['54','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['53','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDnC2iSygg
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 611 iterations in 0.311s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.75  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.53/0.75  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.53/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.75  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.53/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.75  thf(d1_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.75         (((X14) != (X13))
% 0.53/0.75          | (r2_hidden @ X14 @ X15)
% 0.53/0.75          | ((X15) != (k1_tarski @ X13)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('1', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.53/0.75      inference('simplify', [status(thm)], ['0'])).
% 0.53/0.75  thf(d3_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf(t1_tex_2, conjecture,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.53/0.75           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i]:
% 0.53/0.75        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.75          ( ![B:$i]:
% 0.53/0.75            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.53/0.75              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.53/0.75  thf('3', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.75          | (r2_hidden @ X0 @ X2)
% 0.53/0.75          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['2', '5'])).
% 0.53/0.75  thf(d1_tex_2, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.75       ( ( v1_zfmisc_1 @ A ) <=>
% 0.53/0.75         ( ?[B:$i]:
% 0.53/0.75           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X28 : $i]:
% 0.53/0.75         (~ (v1_zfmisc_1 @ X28)
% 0.53/0.75          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_1 @ X28)))
% 0.53/0.75          | (v1_xboole_0 @ X28))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X28 : $i]:
% 0.53/0.75         (~ (v1_zfmisc_1 @ X28)
% 0.53/0.75          | (m1_subset_1 @ (sk_B_1 @ X28) @ X28)
% 0.53/0.75          | (v1_xboole_0 @ X28))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.53/0.75  thf(redefinition_k6_domain_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.53/0.75       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X26 : $i, X27 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X26)
% 0.53/0.75          | ~ (m1_subset_1 @ X27 @ X26)
% 0.53/0.75          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.53/0.75          | (v1_xboole_0 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['10'])).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['7', '11'])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.75  thf(t69_enumset1, axiom,
% 0.53/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.53/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.75  thf(l51_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i]:
% 0.53/0.75         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.53/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('18', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.53/0.75      inference('simplify', [status(thm)], ['17'])).
% 0.53/0.75  thf(t12_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]:
% 0.53/0.75         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.75  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.75  thf('21', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '20'])).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k3_tarski @ X0) = (sk_B_1 @ X0))
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['13', '21'])).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((X0) = (k1_tarski @ (k3_tarski @ X0)))
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['22', '23'])).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | ((X0) = (k1_tarski @ (k3_tarski @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X16 @ X15)
% 0.53/0.75          | ((X16) = (X13))
% 0.53/0.75          | ((X15) != (k1_tarski @ X13)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X13 : $i, X16 : $i]:
% 0.53/0.75         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ((X1) = (k3_tarski @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['25', '27'])).
% 0.53/0.75  thf('29', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ sk_A @ X0)
% 0.53/0.75          | ((sk_C @ X0 @ sk_A) = (k3_tarski @ sk_B_2))
% 0.53/0.75          | (v1_xboole_0 @ sk_B_2)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['6', '28'])).
% 0.53/0.75  thf('30', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ sk_A @ X0)
% 0.53/0.75          | ((sk_C @ X0 @ sk_A) = (k3_tarski @ sk_B_2))
% 0.53/0.75          | (v1_xboole_0 @ sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.53/0.75  thf('32', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('33', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_C @ X0 @ sk_A) = (k3_tarski @ sk_B_2)) | (r1_tarski @ sk_A @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['31', '32'])).
% 0.53/0.75  thf('34', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ (k3_tarski @ sk_B_2) @ X0)
% 0.53/0.75          | (r1_tarski @ sk_A @ X0)
% 0.53/0.75          | (r1_tarski @ sk_A @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.75  thf('36', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B_2) @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['35'])).
% 0.53/0.75  thf('37', plain, ((r1_tarski @ sk_A @ (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '36'])).
% 0.53/0.75  thf(t1_mcart_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.53/0.75          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X25 : $i]:
% 0.53/0.75         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X13 : $i, X16 : $i]:
% 0.53/0.75         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.75  thf('40', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.53/0.75          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.75  thf(t1_boole, axiom,
% 0.53/0.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.75  thf('41', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.75  thf(t49_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('42', plain,
% 0.53/0.75      (![X23 : $i, X24 : $i]:
% 0.53/0.75         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.53/0.75  thf('43', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.53/0.75  thf('44', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      (![X25 : $i]:
% 0.53/0.75         (((X25) = (k1_xboole_0)) | (r1_xboole_0 @ (sk_B @ X25) @ X25))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.53/0.75  thf('46', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X0 @ (k1_tarski @ X0))
% 0.53/0.75          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['44', '45'])).
% 0.53/0.75  thf('47', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.53/0.75  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ X0))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.53/0.75  thf(t68_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.53/0.75       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ X10 @ X11)
% 0.53/0.75          | (v1_xboole_0 @ X12)
% 0.53/0.75          | ~ (r1_tarski @ X12 @ X10)
% 0.53/0.75          | ~ (r1_tarski @ X12 @ X11))),
% 0.53/0.75      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.53/0.75  thf('50', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.53/0.75          | ~ (r1_tarski @ X1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.75  thf('51', plain,
% 0.53/0.75      (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['37', '50'])).
% 0.53/0.75  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('53', plain, (~ (r1_tarski @ sk_A @ (k3_tarski @ sk_B_2))),
% 0.53/0.75      inference('clc', [status(thm)], ['51', '52'])).
% 0.53/0.75  thf('54', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('55', plain,
% 0.53/0.75      (![X13 : $i, X17 : $i]:
% 0.53/0.75         (((X17) = (k1_tarski @ X13))
% 0.53/0.75          | ((sk_C_1 @ X17 @ X13) = (X13))
% 0.53/0.75          | (r2_hidden @ (sk_C_1 @ X17 @ X13) @ X17))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('56', plain,
% 0.53/0.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.75  thf('57', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | ((sk_A) = (k1_tarski @ X0))
% 0.53/0.75          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['55', '56'])).
% 0.53/0.75  thf('58', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | ((X0) = (k1_tarski @ (k3_tarski @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.75  thf('59', plain, ((r1_tarski @ sk_A @ (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '36'])).
% 0.53/0.75  thf('60', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]:
% 0.53/0.75         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.75  thf('61', plain,
% 0.53/0.75      (((k2_xboole_0 @ sk_A @ (k1_tarski @ (k3_tarski @ sk_B_2)))
% 0.53/0.75         = (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      ((((k2_xboole_0 @ sk_A @ sk_B_2) = (k1_tarski @ (k3_tarski @ sk_B_2)))
% 0.53/0.75        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2))),
% 0.53/0.75      inference('sup+', [status(thm)], ['58', '61'])).
% 0.53/0.75  thf('63', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]:
% 0.53/0.75         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.75  thf('65', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.75  thf('66', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('67', plain,
% 0.53/0.75      ((((sk_B_2) = (k1_tarski @ (k3_tarski @ sk_B_2)))
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['62', '65', '66'])).
% 0.53/0.75  thf('68', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('69', plain, (((sk_B_2) = (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('clc', [status(thm)], ['67', '68'])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (![X13 : $i, X16 : $i]:
% 0.53/0.75         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ sk_B_2) | ((X0) = (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.75  thf('72', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_A) = (k1_tarski @ X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['57', '71'])).
% 0.53/0.75  thf('73', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | ((X0) = (k1_tarski @ (k3_tarski @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (![X25 : $i]:
% 0.53/0.75         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.53/0.75  thf('76', plain,
% 0.53/0.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.75  thf('77', plain,
% 0.53/0.75      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['75', '76'])).
% 0.53/0.75  thf('78', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.53/0.75          | ~ (v1_zfmisc_1 @ X0)
% 0.53/0.75          | (v1_xboole_0 @ X0)
% 0.53/0.75          | ((X1) = (k3_tarski @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['25', '27'])).
% 0.53/0.75  thf('79', plain,
% 0.53/0.75      ((((sk_A) = (k1_xboole_0))
% 0.53/0.75        | ((sk_B @ sk_A) = (k3_tarski @ sk_B_2))
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2)
% 0.53/0.75        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['77', '78'])).
% 0.53/0.75  thf('80', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('81', plain,
% 0.53/0.75      ((((sk_A) = (k1_xboole_0))
% 0.53/0.75        | ((sk_B @ sk_A) = (k3_tarski @ sk_B_2))
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['79', '80'])).
% 0.53/0.75  thf('82', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      ((((sk_B @ sk_A) = (k3_tarski @ sk_B_2)) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('clc', [status(thm)], ['81', '82'])).
% 0.53/0.75  thf('84', plain,
% 0.53/0.75      (![X25 : $i]:
% 0.53/0.75         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.53/0.75  thf('85', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      (![X13 : $i, X16 : $i]:
% 0.53/0.75         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.75  thf('87', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.53/0.75          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['85', '86'])).
% 0.53/0.75  thf('88', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('89', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.75          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.53/0.75          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['87', '88'])).
% 0.53/0.75  thf('90', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.75      inference('simplify', [status(thm)], ['89'])).
% 0.53/0.75  thf('91', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['84', '90'])).
% 0.53/0.75  thf('92', plain,
% 0.53/0.75      (((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_A)
% 0.53/0.75        | ((sk_A) = (k1_xboole_0))
% 0.53/0.75        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['83', '91'])).
% 0.53/0.75  thf('93', plain,
% 0.53/0.75      ((((sk_A) = (k1_xboole_0))
% 0.53/0.75        | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_A))),
% 0.53/0.75      inference('simplify', [status(thm)], ['92'])).
% 0.53/0.75  thf('94', plain,
% 0.53/0.75      (((r1_tarski @ sk_B_2 @ sk_A)
% 0.53/0.75        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2)
% 0.53/0.75        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['74', '93'])).
% 0.53/0.75  thf('95', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('96', plain,
% 0.53/0.75      (((r1_tarski @ sk_B_2 @ sk_A)
% 0.53/0.75        | (v1_xboole_0 @ sk_B_2)
% 0.53/0.75        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['94', '95'])).
% 0.53/0.75  thf('97', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('98', plain,
% 0.53/0.75      (![X4 : $i, X6 : $i]:
% 0.53/0.75         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('99', plain, ((~ (r1_tarski @ sk_B_2 @ sk_A) | ((sk_B_2) = (sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.53/0.75  thf('100', plain, (((sk_A) != (sk_B_2))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('101', plain, (~ (r1_tarski @ sk_B_2 @ sk_A)),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 0.53/0.75  thf('102', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_2))),
% 0.53/0.75      inference('clc', [status(thm)], ['96', '101'])).
% 0.53/0.75  thf('103', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.75      inference('clc', [status(thm)], ['102', '103'])).
% 0.53/0.75  thf('105', plain, (![X0 : $i]: ((k1_tarski @ X0) != (sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['73', '104'])).
% 0.53/0.75  thf('106', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['72', '105'])).
% 0.53/0.75  thf('107', plain,
% 0.53/0.75      (![X13 : $i, X17 : $i]:
% 0.53/0.75         (((X17) = (k1_tarski @ X13))
% 0.53/0.75          | ((sk_C_1 @ X17 @ X13) = (X13))
% 0.53/0.75          | (r2_hidden @ (sk_C_1 @ X17 @ X13) @ X17))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('108', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.75      inference('simplify', [status(thm)], ['89'])).
% 0.53/0.75  thf('109', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((sk_C_1 @ X0 @ X1) = (X1))
% 0.53/0.75          | ((X0) = (k1_tarski @ X1))
% 0.53/0.75          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ X1)) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['107', '108'])).
% 0.53/0.75  thf('110', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_A)
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | ((sk_A) = (k1_tarski @ X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['106', '109'])).
% 0.53/0.75  thf('111', plain, (((sk_B_2) = (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.53/0.75      inference('clc', [status(thm)], ['67', '68'])).
% 0.53/0.75  thf('112', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_tarski @ sk_B_2 @ sk_A)
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | ((sk_A) = (k1_tarski @ X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['110', '111'])).
% 0.53/0.75  thf('113', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_A) = (k1_tarski @ X0))
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 0.53/0.75          | (r1_tarski @ sk_B_2 @ sk_A))),
% 0.53/0.75      inference('simplify', [status(thm)], ['112'])).
% 0.53/0.75  thf('114', plain, (![X0 : $i]: ((k1_tarski @ X0) != (sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['73', '104'])).
% 0.53/0.75  thf('115', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((sk_C_1 @ sk_A @ X0) = (X0)) | (r1_tarski @ sk_B_2 @ sk_A))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 0.53/0.75  thf('116', plain, (~ (r1_tarski @ sk_B_2 @ sk_A)),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 0.53/0.75  thf('117', plain, (![X0 : $i]: ((sk_C_1 @ sk_A @ X0) = (X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['115', '116'])).
% 0.53/0.75  thf('118', plain,
% 0.53/0.75      (![X13 : $i, X17 : $i]:
% 0.53/0.75         (((X17) = (k1_tarski @ X13))
% 0.53/0.75          | ((sk_C_1 @ X17 @ X13) != (X13))
% 0.53/0.75          | ~ (r2_hidden @ (sk_C_1 @ X17 @ X13) @ X17))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('119', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.75          | ((sk_C_1 @ sk_A @ X0) != (X0))
% 0.53/0.75          | ((sk_A) = (k1_tarski @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['117', '118'])).
% 0.53/0.75  thf('120', plain, (![X0 : $i]: ((sk_C_1 @ sk_A @ X0) = (X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['115', '116'])).
% 0.53/0.75  thf('121', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.75          | ((X0) != (X0))
% 0.53/0.75          | ((sk_A) = (k1_tarski @ X0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['119', '120'])).
% 0.53/0.75  thf('122', plain,
% 0.53/0.75      (![X0 : $i]: (((sk_A) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.75      inference('simplify', [status(thm)], ['121'])).
% 0.53/0.75  thf('123', plain, (![X0 : $i]: ((k1_tarski @ X0) != (sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['73', '104'])).
% 0.53/0.75  thf('124', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.53/0.75  thf('125', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.53/0.75      inference('sup-', [status(thm)], ['54', '124'])).
% 0.53/0.75  thf('126', plain, ($false), inference('demod', [status(thm)], ['53', '125'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
