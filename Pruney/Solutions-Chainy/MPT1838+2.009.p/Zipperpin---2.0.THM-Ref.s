%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ntpke2Ln8Y

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 156 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   21
%              Number of atoms          :  607 (1116 expanded)
%              Number of equality atoms :   61 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X40: $i] :
      ( ~ ( v1_zfmisc_1 @ X40 )
      | ( X40
        = ( k6_domain_1 @ X40 @ ( sk_B_1 @ X40 ) ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X40: $i] :
      ( ~ ( v1_zfmisc_1 @ X40 )
      | ( m1_subset_1 @ ( sk_B_1 @ X40 ) @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( ( k6_domain_1 @ X38 @ X39 )
        = ( k1_tarski @ X39 ) ) ) ),
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
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = X34 )
      | ( ( k1_tarski @ X35 )
       != ( k2_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != ( k2_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k2_xboole_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['23','24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('56',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','35','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect+',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ntpke2Ln8Y
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.20/2.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.20/2.37  % Solved by: fo/fo7.sh
% 2.20/2.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.20/2.37  % done 4547 iterations in 1.922s
% 2.20/2.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.20/2.37  % SZS output start Refutation
% 2.20/2.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.20/2.37  thf(sk_B_type, type, sk_B: $i > $i).
% 2.20/2.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.20/2.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.20/2.37  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.20/2.37  thf(sk_A_type, type, sk_A: $i).
% 2.20/2.37  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 2.20/2.37  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.20/2.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.20/2.37  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.20/2.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.20/2.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.20/2.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.20/2.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.20/2.37  thf(t1_tex_2, conjecture,
% 2.20/2.37    (![A:$i]:
% 2.20/2.37     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.20/2.37       ( ![B:$i]:
% 2.20/2.37         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 2.20/2.37           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 2.20/2.37  thf(zf_stmt_0, negated_conjecture,
% 2.20/2.37    (~( ![A:$i]:
% 2.20/2.37        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.20/2.37          ( ![B:$i]:
% 2.20/2.37            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 2.20/2.37              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 2.20/2.37    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 2.20/2.37  thf('0', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 2.20/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.37  thf(d1_tex_2, axiom,
% 2.20/2.37    (![A:$i]:
% 2.20/2.37     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.20/2.37       ( ( v1_zfmisc_1 @ A ) <=>
% 2.20/2.37         ( ?[B:$i]:
% 2.20/2.37           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 2.20/2.37  thf('1', plain,
% 2.20/2.37      (![X40 : $i]:
% 2.20/2.37         (~ (v1_zfmisc_1 @ X40)
% 2.20/2.37          | ((X40) = (k6_domain_1 @ X40 @ (sk_B_1 @ X40)))
% 2.20/2.37          | (v1_xboole_0 @ X40))),
% 2.20/2.37      inference('cnf', [status(esa)], [d1_tex_2])).
% 2.20/2.37  thf('2', plain,
% 2.20/2.37      (![X40 : $i]:
% 2.20/2.37         (~ (v1_zfmisc_1 @ X40)
% 2.20/2.38          | (m1_subset_1 @ (sk_B_1 @ X40) @ X40)
% 2.20/2.38          | (v1_xboole_0 @ X40))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_tex_2])).
% 2.20/2.38  thf(redefinition_k6_domain_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.20/2.38       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 2.20/2.38  thf('3', plain,
% 2.20/2.38      (![X38 : $i, X39 : $i]:
% 2.20/2.38         ((v1_xboole_0 @ X38)
% 2.20/2.38          | ~ (m1_subset_1 @ X39 @ X38)
% 2.20/2.38          | ((k6_domain_1 @ X38 @ X39) = (k1_tarski @ X39)))),
% 2.20/2.38      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.20/2.38  thf('4', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((v1_xboole_0 @ X0)
% 2.20/2.38          | ~ (v1_zfmisc_1 @ X0)
% 2.20/2.38          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 2.20/2.38          | (v1_xboole_0 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['2', '3'])).
% 2.20/2.38  thf('5', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 2.20/2.38          | ~ (v1_zfmisc_1 @ X0)
% 2.20/2.38          | (v1_xboole_0 @ X0))),
% 2.20/2.38      inference('simplify', [status(thm)], ['4'])).
% 2.20/2.38  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(t12_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.20/2.38  thf('7', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('8', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf(t7_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.20/2.38  thf('9', plain,
% 2.20/2.38      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.20/2.38  thf('10', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('11', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.20/2.38           = (k2_xboole_0 @ X1 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['9', '10'])).
% 2.20/2.38  thf(t44_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.20/2.38          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.20/2.38          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 2.20/2.38  thf('12', plain,
% 2.20/2.38      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.20/2.38         (((X33) = (k1_xboole_0))
% 2.20/2.38          | ((X34) = (k1_xboole_0))
% 2.20/2.38          | ((X33) = (X34))
% 2.20/2.38          | ((k1_tarski @ X35) != (k2_xboole_0 @ X33 @ X34)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 2.20/2.38  thf('13', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.20/2.38         (((k1_tarski @ X2) != (k2_xboole_0 @ X1 @ X0))
% 2.20/2.38          | ((X1) = (k2_xboole_0 @ X1 @ X0))
% 2.20/2.38          | ((k2_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.20/2.38          | ((X1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['11', '12'])).
% 2.20/2.38  thf('14', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((k1_tarski @ X0) != (sk_B_2))
% 2.20/2.38          | ((sk_A) = (k1_xboole_0))
% 2.20/2.38          | ((k2_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.20/2.38          | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_B_2)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['8', '13'])).
% 2.20/2.38  thf('15', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('17', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((k1_tarski @ X0) != (sk_B_2))
% 2.20/2.38          | ((sk_A) = (k1_xboole_0))
% 2.20/2.38          | ((sk_B_2) = (k1_xboole_0))
% 2.20/2.38          | ((sk_A) = (sk_B_2)))),
% 2.20/2.38      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.20/2.38  thf('18', plain, (((sk_A) != (sk_B_2))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(d1_xboole_0, axiom,
% 2.20/2.38    (![A:$i]:
% 2.20/2.38     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.20/2.38  thf('19', plain,
% 2.20/2.38      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.20/2.38  thf('20', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(d3_tarski, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ B ) <=>
% 2.20/2.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.20/2.38  thf('21', plain,
% 2.20/2.38      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X5 @ X6)
% 2.20/2.38          | (r2_hidden @ X5 @ X7)
% 2.20/2.38          | ~ (r1_tarski @ X6 @ X7))),
% 2.20/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.20/2.38  thf('22', plain,
% 2.20/2.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['20', '21'])).
% 2.20/2.38  thf('23', plain,
% 2.20/2.38      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['19', '22'])).
% 2.20/2.38  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('25', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 2.20/2.38      inference('clc', [status(thm)], ['23', '24'])).
% 2.20/2.38  thf(l1_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.20/2.38  thf('26', plain,
% 2.20/2.38      (![X30 : $i, X32 : $i]:
% 2.20/2.38         ((r1_tarski @ (k1_tarski @ X30) @ X32) | ~ (r2_hidden @ X30 @ X32))),
% 2.20/2.38      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.20/2.38  thf('27', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 2.20/2.38      inference('sup-', [status(thm)], ['25', '26'])).
% 2.20/2.38  thf('28', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('29', plain,
% 2.20/2.38      (((k2_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2) = (sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['27', '28'])).
% 2.20/2.38  thf(commutativity_k2_xboole_0, axiom,
% 2.20/2.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.20/2.38  thf('30', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.20/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.20/2.38  thf('31', plain,
% 2.20/2.38      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ (sk_B @ sk_A))) = (sk_B_2))),
% 2.20/2.38      inference('demod', [status(thm)], ['29', '30'])).
% 2.20/2.38  thf('32', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.20/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.20/2.38  thf(t49_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 2.20/2.38  thf('33', plain,
% 2.20/2.38      (![X36 : $i, X37 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ (k1_tarski @ X36) @ X37) != (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 2.20/2.38  thf('34', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['32', '33'])).
% 2.20/2.38  thf('35', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['31', '34'])).
% 2.20/2.38  thf('36', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 2.20/2.38      inference('sup-', [status(thm)], ['25', '26'])).
% 2.20/2.38  thf('37', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 2.20/2.38      inference('sup-', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('38', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.20/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.20/2.38  thf(t43_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.20/2.38       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.20/2.38  thf('39', plain,
% 2.20/2.38      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.20/2.38         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 2.20/2.38          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.20/2.38  thf('40', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.20/2.38         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.20/2.38          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 2.20/2.38      inference('sup-', [status(thm)], ['38', '39'])).
% 2.20/2.38  thf('41', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (~ (r1_tarski @ X0 @ sk_B_2)
% 2.20/2.38          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B_2) @ sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['37', '40'])).
% 2.20/2.38  thf('42', plain,
% 2.20/2.38      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2) @ sk_A)),
% 2.20/2.38      inference('sup-', [status(thm)], ['36', '41'])).
% 2.20/2.38  thf('43', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('44', plain,
% 2.20/2.38      (((k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2) @ 
% 2.20/2.38         sk_A) = (sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['42', '43'])).
% 2.20/2.38  thf('45', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.20/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.20/2.38  thf('46', plain,
% 2.20/2.38      (((k2_xboole_0 @ sk_A @ 
% 2.20/2.38         (k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)) = (sk_A))),
% 2.20/2.38      inference('demod', [status(thm)], ['44', '45'])).
% 2.20/2.38  thf('47', plain,
% 2.20/2.38      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.20/2.38  thf('48', plain,
% 2.20/2.38      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.20/2.38  thf('49', plain,
% 2.20/2.38      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X5 @ X6)
% 2.20/2.38          | (r2_hidden @ X5 @ X7)
% 2.20/2.38          | ~ (r1_tarski @ X6 @ X7))),
% 2.20/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.20/2.38  thf('50', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.20/2.38         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 2.20/2.38      inference('sup-', [status(thm)], ['48', '49'])).
% 2.20/2.38  thf('51', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((v1_xboole_0 @ X0)
% 2.20/2.38          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['47', '50'])).
% 2.20/2.38  thf('52', plain,
% 2.20/2.38      (((r2_hidden @ (sk_B @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 2.20/2.38      inference('sup+', [status(thm)], ['46', '51'])).
% 2.20/2.38  thf('53', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('54', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 2.20/2.38      inference('clc', [status(thm)], ['52', '53'])).
% 2.20/2.38  thf('55', plain,
% 2.20/2.38      (![X30 : $i, X32 : $i]:
% 2.20/2.38         ((r1_tarski @ (k1_tarski @ X30) @ X32) | ~ (r2_hidden @ X30 @ X32))),
% 2.20/2.38      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.20/2.38  thf('56', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A)),
% 2.20/2.38      inference('sup-', [status(thm)], ['54', '55'])).
% 2.20/2.38  thf('57', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('58', plain,
% 2.20/2.38      (((k2_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A) = (sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['56', '57'])).
% 2.20/2.38  thf('59', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.20/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.20/2.38  thf('60', plain,
% 2.20/2.38      (((k2_xboole_0 @ sk_A @ (k1_tarski @ (sk_B @ sk_A))) = (sk_A))),
% 2.20/2.38      inference('demod', [status(thm)], ['58', '59'])).
% 2.20/2.38  thf('61', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['32', '33'])).
% 2.20/2.38  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['60', '61'])).
% 2.20/2.38  thf('63', plain, (![X0 : $i]: ((k1_tarski @ X0) != (sk_B_2))),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['17', '18', '35', '62'])).
% 2.20/2.38  thf('64', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 2.20/2.38          | (v1_xboole_0 @ X0)
% 2.20/2.38          | ~ (v1_zfmisc_1 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['5', '63'])).
% 2.20/2.38  thf('65', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((X0) != (sk_B_2))
% 2.20/2.38          | (v1_xboole_0 @ X0)
% 2.20/2.38          | ~ (v1_zfmisc_1 @ X0)
% 2.20/2.38          | ~ (v1_zfmisc_1 @ X0)
% 2.20/2.38          | (v1_xboole_0 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['1', '64'])).
% 2.20/2.38  thf('66', plain, ((~ (v1_zfmisc_1 @ sk_B_2) | (v1_xboole_0 @ sk_B_2))),
% 2.20/2.38      inference('simplify', [status(thm)], ['65'])).
% 2.20/2.38  thf('67', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('68', plain, ((v1_xboole_0 @ sk_B_2)),
% 2.20/2.38      inference('simplify_reflect+', [status(thm)], ['66', '67'])).
% 2.20/2.38  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 2.20/2.38  
% 2.20/2.38  % SZS output end Refutation
% 2.20/2.38  
% 2.20/2.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
