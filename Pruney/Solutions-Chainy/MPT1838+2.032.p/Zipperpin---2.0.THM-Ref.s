%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bblO4FfkJh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 255 expanded)
%              Number of leaves         :   36 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  841 (1934 expanded)
%              Number of equality atoms :   76 ( 148 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
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
    ! [X46: $i] :
      ( ~ ( v1_zfmisc_1 @ X46 )
      | ( X46
        = ( k6_domain_1 @ X46 @ ( sk_B_1 @ X46 ) ) )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X46: $i] :
      ( ~ ( v1_zfmisc_1 @ X46 )
      | ( m1_subset_1 @ ( sk_B_1 @ X46 ) @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
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

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = X30 )
      | ( ( k1_tarski @ X31 )
       != ( k2_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = X30 )
      | ( ( k1_tarski @ X31 )
       != ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['20','21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['28','29'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( m1_subset_1 @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['48','51'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['48','51'])).

thf('56',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('57',plain,
    ( ( ( k6_domain_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_domain_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('67',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X32 ) @ X33 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['28','29'])).

thf('72',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('73',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_2 @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('77',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('78',plain,
    ( ( ( k6_domain_1 @ sk_B_2 @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k6_domain_1 @ sk_B_2 @ ( sk_B @ sk_A ) )
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('87',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X32 ) @ X33 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('89',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['22','70','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bblO4FfkJh
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:02:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 589 iterations in 0.259s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.49/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.49/0.72  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.49/0.72  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.49/0.72  thf(t1_tex_2, conjecture,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.49/0.72           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]:
% 0.49/0.72        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.72          ( ![B:$i]:
% 0.49/0.72            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.49/0.72              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.49/0.72  thf('0', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d1_tex_2, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.72       ( ( v1_zfmisc_1 @ A ) <=>
% 0.49/0.72         ( ?[B:$i]:
% 0.49/0.72           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (![X46 : $i]:
% 0.49/0.72         (~ (v1_zfmisc_1 @ X46)
% 0.49/0.72          | ((X46) = (k6_domain_1 @ X46 @ (sk_B_1 @ X46)))
% 0.49/0.72          | (v1_xboole_0 @ X46))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X46 : $i]:
% 0.49/0.72         (~ (v1_zfmisc_1 @ X46)
% 0.49/0.72          | (m1_subset_1 @ (sk_B_1 @ X46) @ X46)
% 0.49/0.72          | (v1_xboole_0 @ X46))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.49/0.72  thf(redefinition_k6_domain_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.49/0.72       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X44 : $i, X45 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X44)
% 0.49/0.72          | ~ (m1_subset_1 @ X45 @ X44)
% 0.49/0.72          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X0)
% 0.49/0.72          | ~ (v1_zfmisc_1 @ X0)
% 0.49/0.72          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.49/0.72          | (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.49/0.72          | ~ (v1_zfmisc_1 @ X0)
% 0.49/0.72          | (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['4'])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.49/0.72          | (v1_xboole_0 @ X0)
% 0.49/0.72          | ~ (v1_zfmisc_1 @ X0)
% 0.49/0.72          | (v1_xboole_0 @ X0)
% 0.49/0.72          | ~ (v1_zfmisc_1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['1', '5'])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_zfmisc_1 @ X0)
% 0.49/0.72          | (v1_xboole_0 @ X0)
% 0.49/0.72          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.49/0.72      inference('simplify', [status(thm)], ['6'])).
% 0.49/0.72  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(t12_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      (![X16 : $i, X17 : $i]:
% 0.49/0.72         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.49/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.49/0.72  thf(l51_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X27 : $i, X28 : $i]:
% 0.49/0.72         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      (![X16 : $i, X17 : $i]:
% 0.49/0.72         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 0.49/0.72          | ~ (r1_tarski @ X17 @ X16))),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('12', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)) = (sk_B_2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['8', '11'])).
% 0.49/0.72  thf(t44_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.49/0.72          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.72          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.72         (((X29) = (k1_xboole_0))
% 0.49/0.72          | ((X30) = (k1_xboole_0))
% 0.49/0.72          | ((X29) = (X30))
% 0.49/0.72          | ((k1_tarski @ X31) != (k2_xboole_0 @ X29 @ X30)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X27 : $i, X28 : $i]:
% 0.49/0.72         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.72         (((X29) = (k1_xboole_0))
% 0.49/0.72          | ((X30) = (k1_xboole_0))
% 0.49/0.72          | ((X29) = (X30))
% 0.49/0.72          | ((k1_tarski @ X31) != (k3_tarski @ (k2_tarski @ X29 @ X30))))),
% 0.49/0.72      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.72  thf('16', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k1_tarski @ X0) != (sk_B_2))
% 0.49/0.72          | ((sk_A) = (sk_B_2))
% 0.49/0.72          | ((sk_B_2) = (k1_xboole_0))
% 0.49/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '15'])).
% 0.49/0.72  thf('17', plain, (((sk_A) != (sk_B_2))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k1_tarski @ X0) != (sk_B_2))
% 0.49/0.72          | ((sk_B_2) = (k1_xboole_0))
% 0.49/0.72          | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((X0) != (sk_B_2))
% 0.49/0.72          | (v1_xboole_0 @ X0)
% 0.49/0.72          | ~ (v1_zfmisc_1 @ X0)
% 0.49/0.72          | ((sk_A) = (k1_xboole_0))
% 0.49/0.72          | ((sk_B_2) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '18'])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      ((((sk_B_2) = (k1_xboole_0))
% 0.49/0.72        | ((sk_A) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.49/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.49/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.49/0.72  thf('21', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      ((((sk_B_2) = (k1_xboole_0))
% 0.49/0.72        | ((sk_A) = (k1_xboole_0))
% 0.49/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.49/0.72      inference('simplify_reflect+', [status(thm)], ['20', '21'])).
% 0.49/0.72  thf(d1_xboole_0, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('25', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d3_tarski, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X3 @ X4)
% 0.49/0.72          | (r2_hidden @ X3 @ X5)
% 0.49/0.72          | ~ (r1_tarski @ X4 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['24', '27'])).
% 0.49/0.72  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('30', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.49/0.72      inference('clc', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf(d4_xboole_0, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.49/0.72       ( ![D:$i]:
% 0.49/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.72           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X7 @ X8)
% 0.49/0.72          | ~ (r2_hidden @ X7 @ X9)
% 0.49/0.72          | (r2_hidden @ X7 @ X10)
% 0.49/0.72          | ((X10) != (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.72      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.49/0.72  thf('32', plain,
% 0.49/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.72         ((r2_hidden @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.49/0.72          | ~ (r2_hidden @ X7 @ X9)
% 0.49/0.72          | ~ (r2_hidden @ X7 @ X8))),
% 0.49/0.72      inference('simplify', [status(thm)], ['31'])).
% 0.49/0.72  thf(t12_setfam_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      (![X37 : $i, X38 : $i]:
% 0.49/0.72         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.49/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.72  thf('34', plain,
% 0.49/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.72         ((r2_hidden @ X7 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))
% 0.49/0.72          | ~ (r2_hidden @ X7 @ X9)
% 0.49/0.72          | ~ (r2_hidden @ X7 @ X8))),
% 0.49/0.72      inference('demod', [status(thm)], ['32', '33'])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (r2_hidden @ (sk_B @ sk_A) @ X0)
% 0.49/0.72          | (r2_hidden @ (sk_B @ sk_A) @ 
% 0.49/0.72             (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B_2))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['30', '34'])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (((v1_xboole_0 @ sk_A)
% 0.49/0.72        | (r2_hidden @ (sk_B @ sk_A) @ 
% 0.49/0.72           (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_2))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['23', '35'])).
% 0.49/0.72  thf('37', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(l32_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X13 : $i, X15 : $i]:
% 0.49/0.72         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.49/0.72          | ~ (r1_tarski @ X13 @ X15))),
% 0.49/0.72      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.72  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.72  thf(t48_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X22 : $i, X23 : $i]:
% 0.49/0.72         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.49/0.72           = (k3_xboole_0 @ X22 @ X23))),
% 0.49/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X37 : $i, X38 : $i]:
% 0.49/0.72         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.49/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      (![X22 : $i, X23 : $i]:
% 0.49/0.72         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.49/0.72           = (k1_setfam_1 @ (k2_tarski @ X22 @ X23)))),
% 0.49/0.72      inference('demod', [status(thm)], ['40', '41'])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.49/0.72         = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_2)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['39', '42'])).
% 0.49/0.72  thf(t3_boole, axiom,
% 0.49/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.72  thf('44', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.72  thf('45', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_2)))),
% 0.49/0.72      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['36', '45'])).
% 0.49/0.72  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('48', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.49/0.72      inference('clc', [status(thm)], ['46', '47'])).
% 0.49/0.72  thf(d2_subset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_xboole_0 @ A ) =>
% 0.49/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.49/0.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      (![X34 : $i, X35 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X34 @ X35)
% 0.49/0.72          | (m1_subset_1 @ X34 @ X35)
% 0.49/0.72          | (v1_xboole_0 @ X35))),
% 0.49/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.72  thf('51', plain,
% 0.49/0.72      (![X34 : $i, X35 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X34 @ X35) | ~ (r2_hidden @ X34 @ X35))),
% 0.49/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.49/0.72  thf('52', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ sk_A)),
% 0.49/0.72      inference('sup-', [status(thm)], ['48', '51'])).
% 0.49/0.72  thf(dt_k6_domain_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.49/0.72       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.49/0.72  thf('53', plain,
% 0.49/0.72      (![X42 : $i, X43 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X42)
% 0.49/0.72          | ~ (m1_subset_1 @ X43 @ X42)
% 0.49/0.72          | (m1_subset_1 @ (k6_domain_1 @ X42 @ X43) @ (k1_zfmisc_1 @ X42)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.49/0.72         (k1_zfmisc_1 @ sk_A))
% 0.49/0.72        | (v1_xboole_0 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.72  thf('55', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ sk_A)),
% 0.49/0.72      inference('sup-', [status(thm)], ['48', '51'])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X44 : $i, X45 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X44)
% 0.49/0.72          | ~ (m1_subset_1 @ X45 @ X44)
% 0.49/0.72          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      ((((k6_domain_1 @ sk_A @ (sk_B @ sk_A)) = (k1_tarski @ (sk_B @ sk_A)))
% 0.49/0.72        | (v1_xboole_0 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.72  thf('58', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      (((k6_domain_1 @ sk_A @ (sk_B @ sk_A)) = (k1_tarski @ (sk_B @ sk_A)))),
% 0.49/0.72      inference('clc', [status(thm)], ['57', '58'])).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_A)) @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.72        | (v1_xboole_0 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['54', '59'])).
% 0.49/0.72  thf('61', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_A)) @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.72      inference('clc', [status(thm)], ['60', '61'])).
% 0.49/0.72  thf(t3_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      (![X39 : $i, X40 : $i]:
% 0.49/0.72         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('64', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A)),
% 0.49/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      (![X16 : $i, X17 : $i]:
% 0.49/0.72         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 0.49/0.72          | ~ (r1_tarski @ X17 @ X16))),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('66', plain,
% 0.49/0.72      (((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A)) = (sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['64', '65'])).
% 0.49/0.72  thf(t49_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k1_tarski @ X32) @ X33) != (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.49/0.72  thf('68', plain,
% 0.49/0.72      (![X27 : $i, X28 : $i]:
% 0.49/0.72         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.49/0.72  thf('69', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X32) @ X33)) != (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.72  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['66', '69'])).
% 0.49/0.72  thf('71', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.49/0.72      inference('clc', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf('72', plain,
% 0.49/0.72      (![X34 : $i, X35 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X34 @ X35) | ~ (r2_hidden @ X34 @ X35))),
% 0.49/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.49/0.72  thf('73', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ sk_B_2)),
% 0.49/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.72  thf('74', plain,
% 0.49/0.72      (![X42 : $i, X43 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X42)
% 0.49/0.72          | ~ (m1_subset_1 @ X43 @ X42)
% 0.49/0.72          | (m1_subset_1 @ (k6_domain_1 @ X42 @ X43) @ (k1_zfmisc_1 @ X42)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      (((m1_subset_1 @ (k6_domain_1 @ sk_B_2 @ (sk_B @ sk_A)) @ 
% 0.49/0.72         (k1_zfmisc_1 @ sk_B_2))
% 0.49/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['73', '74'])).
% 0.49/0.72  thf('76', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ sk_B_2)),
% 0.49/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.72  thf('77', plain,
% 0.49/0.72      (![X44 : $i, X45 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ X44)
% 0.49/0.72          | ~ (m1_subset_1 @ X45 @ X44)
% 0.49/0.72          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.49/0.72  thf('78', plain,
% 0.49/0.72      ((((k6_domain_1 @ sk_B_2 @ (sk_B @ sk_A)) = (k1_tarski @ (sk_B @ sk_A)))
% 0.49/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['76', '77'])).
% 0.49/0.72  thf('79', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      (((k6_domain_1 @ sk_B_2 @ (sk_B @ sk_A)) = (k1_tarski @ (sk_B @ sk_A)))),
% 0.49/0.72      inference('clc', [status(thm)], ['78', '79'])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_A)) @ (k1_zfmisc_1 @ sk_B_2))
% 0.49/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '80'])).
% 0.49/0.72  thf('82', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_A)) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.49/0.72      inference('clc', [status(thm)], ['81', '82'])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      (![X39 : $i, X40 : $i]:
% 0.49/0.72         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('85', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 0.49/0.72      inference('sup-', [status(thm)], ['83', '84'])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      (![X16 : $i, X17 : $i]:
% 0.49/0.72         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 0.49/0.72          | ~ (r1_tarski @ X17 @ X16))),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('87', plain,
% 0.49/0.72      (((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2))
% 0.49/0.72         = (sk_B_2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['85', '86'])).
% 0.49/0.72  thf('88', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X32) @ X33)) != (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.72  thf('89', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['87', '88'])).
% 0.49/0.72  thf('90', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.49/0.72      inference('simplify_reflect-', [status(thm)], ['22', '70', '89'])).
% 0.49/0.72  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
