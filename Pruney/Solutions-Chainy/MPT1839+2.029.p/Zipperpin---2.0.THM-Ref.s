%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4r6aUfXpMd

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:26 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 197 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   24
%              Number of atoms          :  695 (1653 expanded)
%              Number of equality atoms :   48 ( 127 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( X32
        = ( k6_domain_1 @ X32 @ ( sk_B_1 @ X32 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X32: $i] :
      ( ~ ( v1_zfmisc_1 @ X32 )
      | ( m1_subset_1 @ ( sk_B_1 @ X32 ) @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
        = ( sk_B @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('39',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ sk_A )
      | ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ sk_A )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('69',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['62','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4r6aUfXpMd
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.36/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.55  % Solved by: fo/fo7.sh
% 1.36/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.55  % done 2005 iterations in 1.089s
% 1.36/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.55  % SZS output start Refutation
% 1.36/1.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.36/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.36/1.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.36/1.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.36/1.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.55  thf(sk_B_type, type, sk_B: $i > $i).
% 1.36/1.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.36/1.55  thf(t2_tex_2, conjecture,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.36/1.55           ( r1_tarski @ A @ B ) ) ) ))).
% 1.36/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.55    (~( ![A:$i]:
% 1.36/1.55        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.36/1.55          ( ![B:$i]:
% 1.36/1.55            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.36/1.55              ( r1_tarski @ A @ B ) ) ) ) )),
% 1.36/1.55    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 1.36/1.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_2)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf(d1_tex_2, axiom,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.36/1.55       ( ( v1_zfmisc_1 @ A ) <=>
% 1.36/1.55         ( ?[B:$i]:
% 1.36/1.55           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 1.36/1.55  thf('1', plain,
% 1.36/1.55      (![X32 : $i]:
% 1.36/1.55         (~ (v1_zfmisc_1 @ X32)
% 1.36/1.55          | ((X32) = (k6_domain_1 @ X32 @ (sk_B_1 @ X32)))
% 1.36/1.55          | (v1_xboole_0 @ X32))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.36/1.55  thf('2', plain,
% 1.36/1.55      (![X32 : $i]:
% 1.36/1.55         (~ (v1_zfmisc_1 @ X32)
% 1.36/1.55          | (m1_subset_1 @ (sk_B_1 @ X32) @ X32)
% 1.36/1.55          | (v1_xboole_0 @ X32))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.36/1.55  thf(redefinition_k6_domain_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.36/1.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.36/1.55  thf('3', plain,
% 1.36/1.55      (![X30 : $i, X31 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X30)
% 1.36/1.55          | ~ (m1_subset_1 @ X31 @ X30)
% 1.36/1.55          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 1.36/1.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.36/1.55  thf('4', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.36/1.55          | (v1_xboole_0 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.55  thf('5', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0))),
% 1.36/1.55      inference('simplify', [status(thm)], ['4'])).
% 1.36/1.55  thf('6', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['1', '5'])).
% 1.36/1.55  thf('7', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 1.36/1.55      inference('simplify', [status(thm)], ['6'])).
% 1.36/1.55  thf(t3_xboole_0, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.36/1.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.36/1.55  thf('8', plain,
% 1.36/1.55      (![X7 : $i, X8 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.55  thf(d1_tarski, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.36/1.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.36/1.55  thf('9', plain,
% 1.36/1.55      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X21 @ X20)
% 1.36/1.55          | ((X21) = (X18))
% 1.36/1.55          | ((X20) != (k1_tarski @ X18)))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_tarski])).
% 1.36/1.55  thf('10', plain,
% 1.36/1.55      (![X18 : $i, X21 : $i]:
% 1.36/1.55         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.36/1.55      inference('simplify', [status(thm)], ['9'])).
% 1.36/1.55  thf('11', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.36/1.55          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['8', '10'])).
% 1.36/1.55  thf('12', plain,
% 1.36/1.55      (![X7 : $i, X8 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.55  thf('13', plain,
% 1.36/1.55      (![X18 : $i, X21 : $i]:
% 1.36/1.55         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.36/1.55      inference('simplify', [status(thm)], ['9'])).
% 1.36/1.55  thf('14', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.36/1.55          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['12', '13'])).
% 1.36/1.55  thf('15', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (((X0) = (X1))
% 1.36/1.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.36/1.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.36/1.55      inference('sup+', [status(thm)], ['11', '14'])).
% 1.36/1.55  thf('16', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 1.36/1.55      inference('simplify', [status(thm)], ['15'])).
% 1.36/1.55  thf('17', plain,
% 1.36/1.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.55         (((X19) != (X18))
% 1.36/1.55          | (r2_hidden @ X19 @ X20)
% 1.36/1.55          | ((X20) != (k1_tarski @ X18)))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_tarski])).
% 1.36/1.55  thf('18', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 1.36/1.55      inference('simplify', [status(thm)], ['17'])).
% 1.36/1.55  thf(d1_xboole_0, axiom,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.55  thf('19', plain,
% 1.36/1.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.55  thf('20', plain,
% 1.36/1.55      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X9 @ X7)
% 1.36/1.55          | ~ (r2_hidden @ X9 @ X10)
% 1.36/1.55          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.55  thf('21', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.36/1.55          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['19', '20'])).
% 1.36/1.55  thf('22', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))) | (v1_xboole_0 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['18', '21'])).
% 1.36/1.55  thf('23', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((X0) = (sk_B @ (k1_tarski @ X0))) | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['16', '22'])).
% 1.36/1.55  thf('24', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 1.36/1.55      inference('simplify', [status(thm)], ['17'])).
% 1.36/1.55  thf('25', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.55  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['24', '25'])).
% 1.36/1.55  thf('27', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 1.36/1.55      inference('clc', [status(thm)], ['23', '26'])).
% 1.36/1.55  thf('28', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((sk_B_1 @ X0) = (sk_B @ X0))
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['7', '27'])).
% 1.36/1.55  thf('29', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 1.36/1.55      inference('simplify', [status(thm)], ['6'])).
% 1.36/1.55  thf('30', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['28', '29'])).
% 1.36/1.55  thf('31', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 1.36/1.55      inference('simplify', [status(thm)], ['30'])).
% 1.36/1.55  thf('32', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.36/1.55          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['8', '10'])).
% 1.36/1.55  thf('33', plain,
% 1.36/1.55      (![X7 : $i, X8 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.55  thf('34', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r2_hidden @ X0 @ X1)
% 1.36/1.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.36/1.55          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.36/1.55      inference('sup+', [status(thm)], ['32', '33'])).
% 1.36/1.55  thf('35', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.36/1.55      inference('simplify', [status(thm)], ['34'])).
% 1.36/1.55  thf('36', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X0 @ X1)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | (r2_hidden @ (sk_B @ X0) @ X1))),
% 1.36/1.55      inference('sup+', [status(thm)], ['31', '35'])).
% 1.36/1.55  thf(d3_tarski, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.36/1.55  thf('37', plain,
% 1.36/1.55      (![X4 : $i, X6 : $i]:
% 1.36/1.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.36/1.55      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.55  thf('38', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 1.36/1.55      inference('simplify', [status(thm)], ['30'])).
% 1.36/1.55  thf('39', plain,
% 1.36/1.55      (![X18 : $i, X21 : $i]:
% 1.36/1.55         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.36/1.55      inference('simplify', [status(thm)], ['9'])).
% 1.36/1.55  thf('40', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X1 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ((X1) = (sk_B @ X0)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['38', '39'])).
% 1.36/1.55  thf('41', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_tarski @ X0 @ X1)
% 1.36/1.55          | ((sk_C @ X1 @ X0) = (sk_B @ X0))
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['37', '40'])).
% 1.36/1.55  thf('42', plain,
% 1.36/1.55      (![X4 : $i, X6 : $i]:
% 1.36/1.55         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.36/1.55      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.55  thf('43', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (r2_hidden @ (sk_B @ X0) @ X1)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | (r1_tarski @ X0 @ X1)
% 1.36/1.55          | (r1_tarski @ X0 @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['41', '42'])).
% 1.36/1.55  thf('44', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_tarski @ X0 @ X1)
% 1.36/1.55          | (v1_xboole_0 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X0)
% 1.36/1.55          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 1.36/1.55      inference('simplify', [status(thm)], ['43'])).
% 1.36/1.55  thf('45', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((v1_xboole_0 @ X1)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X1)
% 1.36/1.55          | (r1_xboole_0 @ X1 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X1)
% 1.36/1.55          | (v1_xboole_0 @ X1)
% 1.36/1.55          | (r1_tarski @ X1 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['36', '44'])).
% 1.36/1.55  thf('46', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         ((r1_tarski @ X1 @ X0)
% 1.36/1.55          | (r1_xboole_0 @ X1 @ X0)
% 1.36/1.55          | ~ (v1_zfmisc_1 @ X1)
% 1.36/1.55          | (v1_xboole_0 @ X1))),
% 1.36/1.55      inference('simplify', [status(thm)], ['45'])).
% 1.36/1.55  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('48', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (~ (v1_zfmisc_1 @ sk_A)
% 1.36/1.55          | (r1_xboole_0 @ sk_A @ X0)
% 1.36/1.55          | (r1_tarski @ sk_A @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['46', '47'])).
% 1.36/1.55  thf('49', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('50', plain,
% 1.36/1.55      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | (r1_tarski @ sk_A @ X0))),
% 1.36/1.55      inference('demod', [status(thm)], ['48', '49'])).
% 1.36/1.55  thf(t83_xboole_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.36/1.55  thf('51', plain,
% 1.36/1.55      (![X15 : $i, X16 : $i]:
% 1.36/1.55         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 1.36/1.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.36/1.55  thf('52', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((r1_tarski @ sk_A @ X0) | ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['50', '51'])).
% 1.36/1.55  thf(t48_xboole_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.36/1.55  thf('53', plain,
% 1.36/1.55      (![X13 : $i, X14 : $i]:
% 1.36/1.55         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.36/1.55           = (k3_xboole_0 @ X13 @ X14))),
% 1.36/1.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.55  thf('54', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 1.36/1.55          | (r1_tarski @ sk_A @ X0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['52', '53'])).
% 1.36/1.55  thf(t3_boole, axiom,
% 1.36/1.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.55  thf('55', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.55  thf('56', plain,
% 1.36/1.55      (![X13 : $i, X14 : $i]:
% 1.36/1.55         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.36/1.55           = (k3_xboole_0 @ X13 @ X14))),
% 1.36/1.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.55  thf('57', plain,
% 1.36/1.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.55      inference('sup+', [status(thm)], ['55', '56'])).
% 1.36/1.55  thf(t2_boole, axiom,
% 1.36/1.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.36/1.55  thf('58', plain,
% 1.36/1.55      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.55      inference('cnf', [status(esa)], [t2_boole])).
% 1.36/1.55  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.36/1.55      inference('demod', [status(thm)], ['57', '58'])).
% 1.36/1.55  thf('60', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0)) | (r1_tarski @ sk_A @ X0))),
% 1.36/1.55      inference('demod', [status(thm)], ['54', '59'])).
% 1.36/1.55  thf('61', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('62', plain,
% 1.36/1.55      ((~ (v1_xboole_0 @ k1_xboole_0) | (r1_tarski @ sk_A @ sk_B_2))),
% 1.36/1.55      inference('sup-', [status(thm)], ['60', '61'])).
% 1.36/1.55  thf('63', plain,
% 1.36/1.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.36/1.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.55  thf('64', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.55  thf('65', plain,
% 1.36/1.55      (![X15 : $i, X17 : $i]:
% 1.36/1.55         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 1.36/1.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.36/1.55  thf('66', plain,
% 1.36/1.55      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['64', '65'])).
% 1.36/1.55  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.36/1.55      inference('simplify', [status(thm)], ['66'])).
% 1.36/1.55  thf('68', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 1.36/1.55      inference('simplify', [status(thm)], ['17'])).
% 1.36/1.55  thf('69', plain,
% 1.36/1.55      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X9 @ X7)
% 1.36/1.55          | ~ (r2_hidden @ X9 @ X10)
% 1.36/1.55          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.36/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.55  thf('70', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i]:
% 1.36/1.55         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.36/1.55      inference('sup-', [status(thm)], ['68', '69'])).
% 1.36/1.55  thf('71', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.36/1.55      inference('sup-', [status(thm)], ['67', '70'])).
% 1.36/1.55  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.55      inference('sup-', [status(thm)], ['63', '71'])).
% 1.36/1.55  thf('73', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.36/1.55      inference('demod', [status(thm)], ['62', '72'])).
% 1.36/1.55  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 1.36/1.55  
% 1.36/1.55  % SZS output end Refutation
% 1.36/1.55  
% 1.36/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
