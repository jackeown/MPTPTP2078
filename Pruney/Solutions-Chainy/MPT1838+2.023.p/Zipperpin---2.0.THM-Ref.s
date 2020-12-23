%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xUMV0XbaUD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:18 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 149 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  555 (1002 expanded)
%              Number of equality atoms :   51 (  74 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X37 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_xboole_0 @ X34 @ X35 )
      | ~ ( r1_tarski @ X34 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_B_2 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X48: $i] :
      ( ~ ( v1_zfmisc_1 @ X48 )
      | ( X48
        = ( k6_domain_1 @ X48 @ ( sk_B_1 @ X48 ) ) )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('12',plain,(
    ! [X48: $i] :
      ( ~ ( v1_zfmisc_1 @ X48 )
      | ( m1_subset_1 @ ( sk_B_1 @ X48 ) @ X48 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X46: $i,X47: $i] :
      ( ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ X46 )
      | ( ( k6_domain_1 @ X46 @ X47 )
        = ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( r1_tarski @ X38 @ ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_xboole_0 @ X32 @ X33 )
      | ( r1_xboole_0 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ X41 )
        = X40 )
      | ~ ( r1_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B_2 ) @ sk_A )
      | ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( r1_tarski @ X38 @ ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = X44 )
      | ( ( k1_tarski @ X45 )
       != ( k2_xboole_0 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('48',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_xboole_0 @ X34 @ X35 )
      | ~ ( r1_tarski @ X34 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(clc,[status(thm)],['46','51'])).

thf('53',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','54'])).

thf('56',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['10','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xUMV0XbaUD
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:22:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 2318 iterations in 0.538s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.76/0.98  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.76/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.98  thf(t1_tex_2, conjecture,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.76/0.98           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i]:
% 0.76/0.98        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.98          ( ![B:$i]:
% 0.76/0.98            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.76/0.98              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.76/0.98  thf('0', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(l32_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      (![X17 : $i, X19 : $i]:
% 0.76/0.98         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 0.76/0.98          | ~ (r1_tarski @ X17 @ X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.98  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.98  thf(t79_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      (![X36 : $i, X37 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X37)),
% 0.76/0.98      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.76/0.98  thf(symmetry_r1_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (![X8 : $i, X9 : $i]:
% 0.76/0.98         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.76/0.98      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.98  thf(t69_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.98       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i]:
% 0.76/0.98         (~ (r1_xboole_0 @ X34 @ X35)
% 0.76/0.98          | ~ (r1_tarski @ X34 @ X35)
% 0.76/0.98          | (v1_xboole_0 @ X34))),
% 0.76/0.98      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_B_2 @ k1_xboole_0) | (v1_xboole_0 @ sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '7'])).
% 0.76/0.98  thf('9', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('10', plain, (~ (r1_tarski @ sk_B_2 @ k1_xboole_0)),
% 0.76/0.98      inference('clc', [status(thm)], ['8', '9'])).
% 0.76/0.98  thf(d1_tex_2, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.98       ( ( v1_zfmisc_1 @ A ) <=>
% 0.76/0.98         ( ?[B:$i]:
% 0.76/0.98           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X48 : $i]:
% 0.76/0.98         (~ (v1_zfmisc_1 @ X48)
% 0.76/0.98          | ((X48) = (k6_domain_1 @ X48 @ (sk_B_1 @ X48)))
% 0.76/0.98          | (v1_xboole_0 @ X48))),
% 0.76/0.98      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      (![X48 : $i]:
% 0.76/0.98         (~ (v1_zfmisc_1 @ X48)
% 0.76/0.98          | (m1_subset_1 @ (sk_B_1 @ X48) @ X48)
% 0.76/0.98          | (v1_xboole_0 @ X48))),
% 0.76/0.98      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.76/0.98  thf(redefinition_k6_domain_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.76/0.98       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X46 : $i, X47 : $i]:
% 0.76/0.98         ((v1_xboole_0 @ X46)
% 0.76/0.98          | ~ (m1_subset_1 @ X47 @ X46)
% 0.76/0.98          | ((k6_domain_1 @ X46 @ X47) = (k1_tarski @ X47)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_zfmisc_1 @ X0)
% 0.76/0.98          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.76/0.98          | (v1_xboole_0 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.76/0.98          | ~ (v1_zfmisc_1 @ X0)
% 0.76/0.98          | (v1_xboole_0 @ X0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['14'])).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_zfmisc_1 @ X0)
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_zfmisc_1 @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['11', '15'])).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_zfmisc_1 @ X0)
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['16'])).
% 0.76/0.98  thf(t1_boole, axiom,
% 0.76/0.98    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.98  thf('18', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [t1_boole])).
% 0.76/0.98  thf(t7_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (![X38 : $i, X39 : $i]: (r1_tarski @ X38 @ (k2_xboole_0 @ X38 @ X39))),
% 0.76/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.98  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf(t43_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.76/0.98       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.98         ((r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X28)
% 0.76/0.98          | ~ (r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.98  thf('24', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t63_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.76/0.98       ( r1_xboole_0 @ A @ C ) ))).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X31 @ X32)
% 0.76/0.98          | ~ (r1_xboole_0 @ X32 @ X33)
% 0.76/0.98          | (r1_xboole_0 @ X31 @ X33))),
% 0.76/0.98      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B_2 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['23', '26'])).
% 0.76/0.98  thf(t83_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (![X40 : $i, X41 : $i]:
% 0.76/0.98         (((k4_xboole_0 @ X40 @ X41) = (X40)) | ~ (r1_xboole_0 @ X40 @ X41))),
% 0.76/0.98      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2)) = (sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B_2) @ sk_A)
% 0.76/0.98          | (v1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      ((v1_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '31'])).
% 0.76/0.98  thf(l13_xboole_0, axiom,
% 0.76/0.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.76/0.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((r1_tarski @ X17 @ X18)
% 0.76/0.98          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | (r1_tarski @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.98  thf('37', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 0.76/0.98      inference('simplify', [status(thm)], ['36'])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (![X38 : $i, X39 : $i]: (r1_tarski @ X38 @ (k2_xboole_0 @ X38 @ X39))),
% 0.76/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (![X14 : $i, X16 : $i]:
% 0.76/0.98         (((X14) = (X16))
% 0.76/0.98          | ~ (r1_tarski @ X16 @ X14)
% 0.76/0.98          | ~ (r1_tarski @ X14 @ X16))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.76/0.98          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('41', plain, (((k2_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['37', '40'])).
% 0.76/0.98  thf(t44_zfmisc_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.76/0.98          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.76/0.98          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.76/0.98  thf('42', plain,
% 0.76/0.98      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.76/0.98         (((X43) = (k1_xboole_0))
% 0.76/0.98          | ((X44) = (k1_xboole_0))
% 0.76/0.98          | ((X43) = (X44))
% 0.76/0.98          | ((k1_tarski @ X45) != (k2_xboole_0 @ X43 @ X44)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k1_tarski @ X0) != (sk_B_2))
% 0.76/0.98          | ((sk_B_2) = (sk_A))
% 0.76/0.98          | ((sk_A) = (k1_xboole_0))
% 0.76/0.98          | ((sk_B_2) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2)) = (sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((r1_tarski @ X17 @ X18)
% 0.76/0.98          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((sk_A) != (k1_xboole_0))
% 0.76/0.98          | (r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.98  thf('47', plain,
% 0.76/0.98      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['23', '26'])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i]:
% 0.76/0.98         (~ (r1_xboole_0 @ X34 @ X35)
% 0.76/0.98          | ~ (r1_tarski @ X34 @ X35)
% 0.76/0.98          | (v1_xboole_0 @ X34))),
% 0.76/0.98      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v1_xboole_0 @ sk_A)
% 0.76/0.98          | ~ (r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.98  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('51', plain,
% 0.76/0.98      (![X0 : $i]: ~ (r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_2))),
% 0.76/0.98      inference('clc', [status(thm)], ['49', '50'])).
% 0.76/0.98  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.76/0.98      inference('clc', [status(thm)], ['46', '51'])).
% 0.76/0.98  thf('53', plain, (((sk_A) != (sk_B_2))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('54', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k1_tarski @ X0) != (sk_B_2)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.76/0.98      inference('simplify_reflect-', [status(thm)], ['43', '52', '53'])).
% 0.76/0.98  thf('55', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((X0) != (sk_B_2))
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_zfmisc_1 @ X0)
% 0.76/0.98          | ((sk_B_2) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['17', '54'])).
% 0.76/0.98  thf('56', plain,
% 0.76/0.98      ((((sk_B_2) = (k1_xboole_0))
% 0.76/0.98        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.76/0.98        | (v1_xboole_0 @ sk_B_2))),
% 0.76/0.98      inference('simplify', [status(thm)], ['55'])).
% 0.76/0.98  thf('57', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('58', plain, ((((sk_B_2) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_2))),
% 0.76/0.98      inference('simplify_reflect+', [status(thm)], ['56', '57'])).
% 0.76/0.98  thf('59', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('60', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.76/0.98      inference('clc', [status(thm)], ['58', '59'])).
% 0.76/0.98  thf('61', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf('62', plain, ($false),
% 0.76/0.98      inference('demod', [status(thm)], ['10', '60', '61'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
