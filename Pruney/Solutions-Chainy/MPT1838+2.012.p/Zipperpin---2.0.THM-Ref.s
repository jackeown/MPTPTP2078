%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PtfnPvOal4

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 150 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :  561 (1065 expanded)
%              Number of equality atoms :   49 (  87 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    r1_tarski @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_3 )
    = sk_B_3 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_3 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_3 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 = X22 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['9','17'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_2 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('20',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_2 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 = X22 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference(clc,[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','42'])).

thf('44',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_2 @ sk_B_3 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_3 )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,(
    v1_zfmisc_1 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_2 @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B @ sk_A )
    = ( sk_B_2 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('50',plain,
    ( ( sk_B_3
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_zfmisc_1 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_zfmisc_1 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B_3
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_B_3
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B_3 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B_3 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_3 )
    = sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B_3 = sk_A ),
    inference('sup+',[status(thm)],['2','64'])).

thf('66',plain,(
    sk_A != sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PtfnPvOal4
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.86  % Solved by: fo/fo7.sh
% 0.69/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.86  % done 995 iterations in 0.414s
% 0.69/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.86  % SZS output start Refutation
% 0.69/0.86  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.86  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.69/0.86  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.69/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.86  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.69/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.86  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.69/0.86  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.69/0.86  thf(t1_tex_2, conjecture,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.69/0.86           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.69/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.86    (~( ![A:$i]:
% 0.69/0.86        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86          ( ![B:$i]:
% 0.69/0.86            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.69/0.86              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.69/0.86    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.69/0.86  thf('0', plain, ((r1_tarski @ sk_A @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t12_xboole_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.69/0.86  thf('1', plain,
% 0.69/0.86      (![X9 : $i, X10 : $i]:
% 0.69/0.86         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.69/0.86  thf('2', plain, (((k2_xboole_0 @ sk_A @ sk_B_3) = (sk_B_3))),
% 0.69/0.86      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.86  thf(d1_xboole_0, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.86  thf('3', plain,
% 0.69/0.86      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.69/0.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.86  thf('4', plain, ((r1_tarski @ sk_A @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(d3_tarski, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.86  thf('5', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X5 @ X6)
% 0.69/0.86          | (r2_hidden @ X5 @ X7)
% 0.69/0.86          | ~ (r1_tarski @ X6 @ X7))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.86  thf('6', plain,
% 0.69/0.86      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_3) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('7', plain,
% 0.69/0.86      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_3))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '6'])).
% 0.69/0.86  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('9', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_3)),
% 0.69/0.86      inference('clc', [status(thm)], ['7', '8'])).
% 0.69/0.86  thf('10', plain,
% 0.69/0.86      (![X6 : $i, X8 : $i]:
% 0.69/0.86         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.86  thf(t17_zfmisc_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ( A ) != ( B ) ) =>
% 0.69/0.86       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.69/0.86  thf('11', plain,
% 0.69/0.86      (![X21 : $i, X22 : $i]:
% 0.69/0.86         ((r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.69/0.86          | ((X21) = (X22)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.69/0.86  thf(l24_zfmisc_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.86  thf('12', plain,
% 0.69/0.86      (![X19 : $i, X20 : $i]:
% 0.69/0.86         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.69/0.86      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.69/0.86  thf('13', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.86  thf('14', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.69/0.86          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['10', '13'])).
% 0.69/0.86  thf('15', plain,
% 0.69/0.86      (![X6 : $i, X8 : $i]:
% 0.69/0.86         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.86  thf('16', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.86          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.69/0.86          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.69/0.86      inference('sup-', [status(thm)], ['14', '15'])).
% 0.69/0.86  thf('17', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.69/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.69/0.86  thf('18', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_3)),
% 0.69/0.86      inference('sup-', [status(thm)], ['9', '17'])).
% 0.69/0.86  thf(d1_tex_2, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86       ( ( v1_zfmisc_1 @ A ) <=>
% 0.69/0.86         ( ?[B:$i]:
% 0.69/0.86           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.69/0.86  thf('19', plain,
% 0.69/0.86      (![X28 : $i]:
% 0.69/0.86         (~ (v1_zfmisc_1 @ X28)
% 0.69/0.86          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_2 @ X28)))
% 0.69/0.86          | (v1_xboole_0 @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.69/0.86  thf('20', plain,
% 0.69/0.86      (![X28 : $i]:
% 0.69/0.86         (~ (v1_zfmisc_1 @ X28)
% 0.69/0.86          | (m1_subset_1 @ (sk_B_2 @ X28) @ X28)
% 0.69/0.86          | (v1_xboole_0 @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.69/0.86  thf(redefinition_k6_domain_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.69/0.86       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.69/0.86  thf('21', plain,
% 0.69/0.86      (![X26 : $i, X27 : $i]:
% 0.69/0.86         ((v1_xboole_0 @ X26)
% 0.69/0.86          | ~ (m1_subset_1 @ X27 @ X26)
% 0.69/0.86          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.69/0.86      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.69/0.86  thf('22', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v1_xboole_0 @ X0)
% 0.69/0.86          | ~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | ((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.69/0.86          | (v1_xboole_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.86  thf('23', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.69/0.86          | ~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | (v1_xboole_0 @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['22'])).
% 0.69/0.86  thf('24', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (((X0) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.69/0.86          | (v1_xboole_0 @ X0)
% 0.69/0.86          | ~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | (v1_xboole_0 @ X0)
% 0.69/0.86          | ~ (v1_zfmisc_1 @ X0))),
% 0.69/0.86      inference('sup+', [status(thm)], ['19', '23'])).
% 0.69/0.86  thf('25', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | (v1_xboole_0 @ X0)
% 0.69/0.86          | ((X0) = (k1_tarski @ (sk_B_2 @ X0))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['24'])).
% 0.69/0.86  thf('26', plain,
% 0.69/0.86      (![X21 : $i, X22 : $i]:
% 0.69/0.86         ((r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.69/0.86          | ((X21) = (X22)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.69/0.86  thf(t69_xboole_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.86       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.69/0.86  thf('27', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (r1_xboole_0 @ X14 @ X15)
% 0.69/0.86          | ~ (r1_tarski @ X14 @ X15)
% 0.69/0.86          | (v1_xboole_0 @ X14))),
% 0.69/0.86      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.69/0.86  thf('28', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (((X1) = (X0))
% 0.69/0.86          | (v1_xboole_0 @ (k1_tarski @ X1))
% 0.69/0.86          | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.86  thf(t1_mcart_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.69/0.86          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.69/0.86  thf('29', plain,
% 0.69/0.86      (![X25 : $i]:
% 0.69/0.86         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X25) @ X25))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.69/0.86  thf('30', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.86  thf('31', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.69/0.86          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.86  thf(t1_boole, axiom,
% 0.69/0.86    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.86  thf('32', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.86  thf(t49_zfmisc_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.69/0.86  thf('33', plain,
% 0.69/0.86      (![X23 : $i, X24 : $i]:
% 0.69/0.86         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.69/0.86      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.69/0.86  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.86  thf('35', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 0.69/0.86      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.69/0.86  thf('36', plain,
% 0.69/0.86      (![X25 : $i]:
% 0.69/0.86         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X25) @ X25))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.69/0.86  thf('37', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.69/0.86          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.69/0.86      inference('sup+', [status(thm)], ['35', '36'])).
% 0.69/0.86  thf('38', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.86  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.86      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.69/0.86  thf('40', plain,
% 0.69/0.86      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.86  thf('41', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.86  thf('42', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)) | ((X1) = (X0)))),
% 0.69/0.86      inference('clc', [status(thm)], ['28', '41'])).
% 0.69/0.86  thf('43', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (r1_tarski @ (k1_tarski @ X1) @ X0)
% 0.69/0.86          | (v1_xboole_0 @ X0)
% 0.69/0.86          | ~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | ((X1) = (sk_B_2 @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['25', '42'])).
% 0.69/0.86  thf('44', plain,
% 0.69/0.86      ((((sk_B @ sk_A) = (sk_B_2 @ sk_B_3))
% 0.69/0.86        | ~ (v1_zfmisc_1 @ sk_B_3)
% 0.69/0.86        | (v1_xboole_0 @ sk_B_3))),
% 0.69/0.86      inference('sup-', [status(thm)], ['18', '43'])).
% 0.69/0.86  thf('45', plain, ((v1_zfmisc_1 @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('46', plain,
% 0.69/0.86      ((((sk_B @ sk_A) = (sk_B_2 @ sk_B_3)) | (v1_xboole_0 @ sk_B_3))),
% 0.69/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.86  thf('47', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('48', plain, (((sk_B @ sk_A) = (sk_B_2 @ sk_B_3))),
% 0.69/0.86      inference('clc', [status(thm)], ['46', '47'])).
% 0.69/0.86  thf('49', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (v1_zfmisc_1 @ X0)
% 0.69/0.86          | (v1_xboole_0 @ X0)
% 0.69/0.86          | ((X0) = (k1_tarski @ (sk_B_2 @ X0))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['24'])).
% 0.69/0.86  thf('50', plain,
% 0.69/0.86      ((((sk_B_3) = (k1_tarski @ (sk_B @ sk_A)))
% 0.69/0.86        | (v1_xboole_0 @ sk_B_3)
% 0.69/0.86        | ~ (v1_zfmisc_1 @ sk_B_3))),
% 0.69/0.86      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.86  thf('51', plain, ((v1_zfmisc_1 @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('52', plain,
% 0.69/0.86      ((((sk_B_3) = (k1_tarski @ (sk_B @ sk_A))) | (v1_xboole_0 @ sk_B_3))),
% 0.69/0.86      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.86  thf('53', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('54', plain, (((sk_B_3) = (k1_tarski @ (sk_B @ sk_A)))),
% 0.69/0.86      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.86  thf('55', plain,
% 0.69/0.86      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.69/0.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.86  thf('56', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.69/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.69/0.86  thf('57', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.86  thf('58', plain, (((r1_tarski @ sk_B_3 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.69/0.86      inference('sup+', [status(thm)], ['54', '57'])).
% 0.69/0.86  thf('59', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('60', plain, ((r1_tarski @ sk_B_3 @ sk_A)),
% 0.69/0.86      inference('clc', [status(thm)], ['58', '59'])).
% 0.69/0.86  thf('61', plain,
% 0.69/0.86      (![X9 : $i, X10 : $i]:
% 0.69/0.86         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.69/0.86  thf('62', plain, (((k2_xboole_0 @ sk_B_3 @ sk_A) = (sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.86  thf(commutativity_k2_xboole_0, axiom,
% 0.69/0.86    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.69/0.86  thf('63', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.86  thf('64', plain, (((k2_xboole_0 @ sk_A @ sk_B_3) = (sk_A))),
% 0.69/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.69/0.86  thf('65', plain, (((sk_B_3) = (sk_A))),
% 0.69/0.86      inference('sup+', [status(thm)], ['2', '64'])).
% 0.69/0.86  thf('66', plain, (((sk_A) != (sk_B_3))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('67', plain, ($false),
% 0.69/0.86      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.69/0.86  
% 0.69/0.86  % SZS output end Refutation
% 0.69/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
