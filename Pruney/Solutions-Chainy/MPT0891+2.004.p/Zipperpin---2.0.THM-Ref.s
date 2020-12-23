%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsmLtKThB1

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 541 expanded)
%              Number of leaves         :   39 ( 179 expanded)
%              Depth                    :   23
%              Number of atoms          : 1524 (9221 expanded)
%              Number of equality atoms :  224 (1400 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X46
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k6_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X46
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k6_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X45 ) )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('33',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','29','30','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['15','44'])).

thf('46',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf('47',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('48',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('50',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_mcart_1 @ X30 @ X31 @ X32 )
      = ( k4_tarski @ ( k4_tarski @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k2_mcart_1 @ X36 ) )
      | ( X36
       != ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('53',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k4_tarski @ X37 @ X38 )
     != ( k2_mcart_1 @ ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('54',plain,(
    ! [X51: $i,X53: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X51 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k4_tarski @ X37 @ X38 )
     != X38 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['50','56'])).

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

thf('58',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('59',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('60',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('63',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('64',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('65',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('67',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ X39 )
      | ( ( sk_B @ X39 )
       != ( k3_mcart_1 @ X41 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('73',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('77',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('78',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X26 @ X28 ) @ X27 )
       != ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
       != ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','83'])).

thf('85',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('86',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['70','87'])).

thf('89',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['61','88'])).

thf('90',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('95',plain,
    ( sk_D_1
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['57','93','94'])).

thf('96',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['45','95'])).

thf('97',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ( ( sk_B @ X39 )
       != ( k3_mcart_1 @ X41 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','98'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('100',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('102',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('103',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('105',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('110',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 != sk_D_1 ) ),
    inference(demod,[status(thm)],['99','112'])).

thf('114',plain,
    ( ( k1_tarski @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('116',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(simplify,[status(thm)],['116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsmLtKThB1
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:18:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 139 iterations in 0.086s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.35/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.54         (((X19) != (X18))
% 0.35/0.54          | (r2_hidden @ X19 @ X20)
% 0.35/0.54          | ((X20) != (k1_tarski @ X18)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('1', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.35/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.35/0.54  thf(t51_mcart_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ~( ![D:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.35/0.54                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.35/0.54                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.35/0.54                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54             ( ~( ![D:$i]:
% 0.35/0.54                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.35/0.54                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.35/0.54                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.35/0.54                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d3_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.35/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.35/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.35/0.54        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf(t50_mcart_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ~( ![D:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.35/0.54                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.35/0.54                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.35/0.54                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.35/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.35/0.54                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k6_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.35/0.54              = (k2_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.35/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k6_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.35/0.54              = (k2_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.54        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.35/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.35/0.54  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.35/0.54        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.35/0.54        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('split', [status(esa)], ['13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.35/0.54         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['12', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.35/0.54        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf(t48_mcart_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ~( ![D:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.35/0.54                 ( ( D ) =
% 0.35/0.54                   ( k3_mcart_1 @
% 0.35/0.54                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.35/0.54                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.35/0.54                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.54         (((X43) = (k1_xboole_0))
% 0.35/0.54          | ((X44) = (k1_xboole_0))
% 0.35/0.54          | ((X46)
% 0.35/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.35/0.54                 (k6_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.35/0.54                 (k7_mcart_1 @ X43 @ X44 @ X45 @ X46)))
% 0.35/0.54          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X43 @ X44 @ X45))
% 0.35/0.54          | ((X45) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.35/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.54         (((X43) = (k1_xboole_0))
% 0.35/0.54          | ((X44) = (k1_xboole_0))
% 0.35/0.54          | ((X46)
% 0.35/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.35/0.54                 (k6_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.35/0.54                 (k7_mcart_1 @ X43 @ X44 @ X45 @ X46)))
% 0.35/0.54          | ~ (m1_subset_1 @ X46 @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X45))
% 0.35/0.54          | ((X45) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_D_1)
% 0.35/0.54            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.35/0.54               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.35/0.54               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.35/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '19'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.35/0.54        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k5_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.35/0.54              = (k1_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.35/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k5_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.35/0.54              = (k1_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.54        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.35/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.35/0.54  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('28', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.35/0.54        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k7_mcart_1 @ X47 @ X48 @ X50 @ X49) = (k2_mcart_1 @ X49))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.35/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.54         (((X47) = (k1_xboole_0))
% 0.35/0.54          | ((X48) = (k1_xboole_0))
% 0.35/0.54          | ((k7_mcart_1 @ X47 @ X48 @ X50 @ X49) = (k2_mcart_1 @ X49))
% 0.35/0.54          | ~ (m1_subset_1 @ X49 @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.35/0.54          | ((X50) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.54        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54            = (k2_mcart_1 @ sk_D_1))
% 0.35/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '34'])).
% 0.35/0.54  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('38', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_D_1)
% 0.35/0.54            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.35/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['20', '29', '30', '39'])).
% 0.35/0.54  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('43', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (((sk_D_1)
% 0.35/0.54         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      ((((sk_D_1)
% 0.35/0.54          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1 @ 
% 0.35/0.54             (k2_mcart_1 @ sk_D_1))))
% 0.35/0.54         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['15', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('split', [status(esa)], ['13'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (((sk_D_1)
% 0.35/0.54         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      ((((sk_D_1)
% 0.35/0.54          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.35/0.54  thf(d3_mcart_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.35/0.54         ((k3_mcart_1 @ X30 @ X31 @ X32)
% 0.35/0.54           = (k4_tarski @ (k4_tarski @ X30 @ X31) @ X32))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.35/0.54  thf(t20_mcart_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.35/0.54       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.35/0.54         (((X36) != (k2_mcart_1 @ X36)) | ((X36) != (k4_tarski @ X37 @ X38)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X37 : $i, X38 : $i]:
% 0.35/0.54         ((k4_tarski @ X37 @ X38) != (k2_mcart_1 @ (k4_tarski @ X37 @ X38)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.35/0.54  thf(t7_mcart_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.35/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (![X51 : $i, X53 : $i]: ((k2_mcart_1 @ (k4_tarski @ X51 @ X53)) = (X53))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.35/0.54  thf('55', plain, (![X37 : $i, X38 : $i]: ((k4_tarski @ X37 @ X38) != (X38))),
% 0.35/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['51', '55'])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['50', '56'])).
% 0.35/0.54  thf(t29_mcart_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.35/0.54                 ( ![C:$i,D:$i,E:$i]:
% 0.35/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.35/0.54                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      (![X39 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X21 @ X20)
% 0.35/0.54          | ((X21) = (X18))
% 0.35/0.54          | ((X20) != (k1_tarski @ X18)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X18 : $i, X21 : $i]:
% 0.35/0.54         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.35/0.54          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['58', '60'])).
% 0.35/0.54  thf('62', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.35/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.35/0.54         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('split', [status(esa)], ['13'])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['63', '64'])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (((sk_D_1)
% 0.35/0.54         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      ((((sk_D_1)
% 0.35/0.54          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.35/0.54             (k2_mcart_1 @ sk_D_1))))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ X41 @ X39)
% 0.35/0.54          | ((sk_B @ X39) != (k3_mcart_1 @ X41 @ X40 @ X42)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      ((![X0 : $i]:
% 0.35/0.54          (((sk_B @ X0) != (sk_D_1))
% 0.35/0.54           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.35/0.54           | ((X0) = (k1_xboole_0))))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.35/0.54         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['62', '69'])).
% 0.35/0.54  thf(t69_enumset1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (![X39 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf(d5_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.35/0.54       ( ![D:$i]:
% 0.35/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('73', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.35/0.54          | (r2_hidden @ X4 @ X1)
% 0.35/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.35/0.54  thf('74', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.35/0.54         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['73'])).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '74'])).
% 0.35/0.54  thf('76', plain,
% 0.35/0.54      (![X39 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.35/0.54          | ~ (r2_hidden @ X4 @ X2)
% 0.35/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.35/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['77'])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['76', '78'])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.35/0.54          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['75', '79'])).
% 0.35/0.54  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['80'])).
% 0.35/0.54  thf(t72_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.35/0.54       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X26 @ X27)
% 0.35/0.54          | ((k4_xboole_0 @ (k2_tarski @ X26 @ X28) @ X27)
% 0.35/0.54              != (k2_tarski @ X26 @ X28)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.35/0.54  thf('83', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.35/0.54          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.35/0.54  thf('84', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.35/0.54          | ((k1_xboole_0) != (k2_tarski @ X0 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['71', '83'])).
% 0.35/0.54  thf('85', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.35/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.35/0.54  thf('86', plain,
% 0.35/0.54      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.54  thf('87', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.35/0.54  thf('88', plain,
% 0.35/0.54      ((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1)))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('clc', [status(thm)], ['70', '87'])).
% 0.35/0.54  thf('89', plain,
% 0.35/0.54      (((((sk_D_1) != (sk_D_1)) | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['61', '88'])).
% 0.35/0.54  thf('90', plain,
% 0.35/0.54      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['89'])).
% 0.35/0.54  thf('91', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.35/0.54  thf('92', plain,
% 0.35/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.35/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.35/0.54  thf('93', plain,
% 0.35/0.54      (~ (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['92'])).
% 0.35/0.54  thf('94', plain,
% 0.35/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.35/0.54       (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.35/0.54       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.35/0.54      inference('split', [status(esa)], ['13'])).
% 0.35/0.54  thf('95', plain,
% 0.35/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['57', '93', '94'])).
% 0.35/0.54  thf('96', plain,
% 0.35/0.54      (((sk_D_1)
% 0.35/0.54         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1 @ 
% 0.35/0.54            (k2_mcart_1 @ sk_D_1)))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['45', '95'])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ X40 @ X39)
% 0.35/0.54          | ((sk_B @ X39) != (k3_mcart_1 @ X41 @ X40 @ X42)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf('98', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((sk_B @ X0) != (sk_D_1))
% 0.35/0.54          | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.35/0.54          | ((X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['96', '97'])).
% 0.35/0.54  thf('99', plain,
% 0.35/0.54      ((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.35/0.54        | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '98'])).
% 0.35/0.54  thf(d1_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.54       ( ![E:$i]:
% 0.35/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.35/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.35/0.54  thf('100', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.35/0.54          | ((X7) = (X8))
% 0.35/0.54          | ((X7) = (X9))
% 0.35/0.54          | ((X7) = (X10)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('101', plain,
% 0.35/0.54      (![X39 : $i]:
% 0.35/0.54         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.35/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.35/0.54  thf(t70_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.54  thf('102', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i]:
% 0.35/0.54         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.54  thf('103', plain,
% 0.35/0.54      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.54  thf('104', plain,
% 0.35/0.54      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['102', '103'])).
% 0.35/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_3, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.54       ( ![E:$i]:
% 0.35/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('105', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X16 @ X15)
% 0.35/0.54          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.35/0.54          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.54  thf('106', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.35/0.54          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['105'])).
% 0.35/0.54  thf('107', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.35/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['104', '106'])).
% 0.35/0.54  thf('108', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.35/0.54          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['101', '107'])).
% 0.35/0.54  thf('109', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.35/0.54  thf('110', plain,
% 0.35/0.54      (![X0 : $i]: ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0)),
% 0.35/0.54      inference('clc', [status(thm)], ['108', '109'])).
% 0.35/0.54  thf('111', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.35/0.54          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.35/0.54          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['100', '110'])).
% 0.35/0.54  thf('112', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['111'])).
% 0.35/0.54  thf('113', plain,
% 0.35/0.54      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)) | ((sk_D_1) != (sk_D_1)))),
% 0.35/0.54      inference('demod', [status(thm)], ['99', '112'])).
% 0.35/0.54  thf('114', plain, (((k1_tarski @ sk_D_1) = (k1_xboole_0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['113'])).
% 0.35/0.54  thf('115', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.35/0.54  thf('116', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['114', '115'])).
% 0.35/0.54  thf('117', plain, ($false), inference('simplify', [status(thm)], ['116'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
