%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2KANlCdjB

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 448 expanded)
%              Number of leaves         :   34 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          : 1236 (8242 expanded)
%              Number of equality atoms :  179 (1281 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X46
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k6_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X46
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k6_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X45 ) )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('8',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('26',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_zfmisc_1 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','15','24','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

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

thf('39',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ X39 )
      | ( ( sk_B @ X39 )
       != ( k3_mcart_1 @ X41 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X26 @ X28 ) @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X24 )
      | ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ~ ( r2_hidden @ X24 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('59',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('63',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['59'])).

thf('64',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('66',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('67',plain,(
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

thf('68',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k2_mcart_1 @ X36 ) )
      | ( X36
       != ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('69',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k4_tarski @ X37 @ X38 )
     != ( k2_mcart_1 @ ( k4_tarski @ X37 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('70',plain,(
    ! [X51: $i,X53: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X51 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('71',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k4_tarski @ X37 @ X38 )
     != X38 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('75',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['59'])).

thf('76',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('79',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ( ( sk_B @ X39 )
       != ( k3_mcart_1 @ X41 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('83',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('87',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['85','87'])).

thf('89',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['59'])).

thf('90',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['73','88','89'])).

thf('91',plain,
    ( sk_D
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['61','90'])).

thf('92',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['57','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2KANlCdjB
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:21:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 103 iterations in 0.045s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(t51_mcart_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ~( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.50                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.50                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50             ( ~( ![D:$i]:
% 0.22/0.50                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.50                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.50                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d3_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.50         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t48_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ~( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50                 ( ( D ) =
% 0.22/0.50                   ( k3_mcart_1 @
% 0.22/0.50                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.50                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.50                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.22/0.50         (((X43) = (k1_xboole_0))
% 0.22/0.50          | ((X44) = (k1_xboole_0))
% 0.22/0.50          | ((X46)
% 0.22/0.50              = (k3_mcart_1 @ (k5_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.22/0.50                 (k6_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.22/0.50                 (k7_mcart_1 @ X43 @ X44 @ X45 @ X46)))
% 0.22/0.50          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X43 @ X44 @ X45))
% 0.22/0.50          | ((X45) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.50         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.22/0.50         (((X43) = (k1_xboole_0))
% 0.22/0.50          | ((X44) = (k1_xboole_0))
% 0.22/0.50          | ((X46)
% 0.22/0.50              = (k3_mcart_1 @ (k5_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.22/0.50                 (k6_mcart_1 @ X43 @ X44 @ X45 @ X46) @ 
% 0.22/0.50                 (k7_mcart_1 @ X43 @ X44 @ X45 @ X46)))
% 0.22/0.50          | ~ (m1_subset_1 @ X46 @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X45))
% 0.22/0.50          | ((X45) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_D)
% 0.22/0.50            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.22/0.50               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.22/0.50               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t50_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ~( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k5_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.22/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.50         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k5_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.22/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.50        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.22/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k6_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.22/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.50         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k6_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 0.22/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X49)))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.50        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.22/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.22/0.50  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k7_mcart_1 @ X47 @ X48 @ X50 @ X49) = (k2_mcart_1 @ X49))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.50         ((k3_zfmisc_1 @ X33 @ X34 @ X35)
% 0.22/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.50         (((X47) = (k1_xboole_0))
% 0.22/0.50          | ((X48) = (k1_xboole_0))
% 0.22/0.50          | ((k7_mcart_1 @ X47 @ X48 @ X50 @ X49) = (k2_mcart_1 @ X49))
% 0.22/0.50          | ~ (m1_subset_1 @ X49 @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48) @ X50))
% 0.22/0.50          | ((X50) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.50        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.22/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.50  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_D)
% 0.22/0.50            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.50               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.22/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '15', '24', '33'])).
% 0.22/0.50  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((sk_D)
% 0.22/0.50         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.50  thf(t29_mcart_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.50                 ( ![C:$i,D:$i,E:$i]:
% 0.22/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.50                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X39 : $i]:
% 0.22/0.50         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.22/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X17 @ X16)
% 0.22/0.50          | ((X17) = (X14))
% 0.22/0.50          | ((X16) != (k1_tarski @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X14 : $i, X17 : $i]:
% 0.22/0.50         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.50          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.50         (((X39) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X41 @ X39)
% 0.22/0.50          | ((sk_B @ X39) != (k3_mcart_1 @ X41 @ X40 @ X42)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))
% 0.22/0.50          | ((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf(t3_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.50  thf(t73_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.50         ((r2_hidden @ X26 @ X27)
% 0.22/0.50          | ((k4_xboole_0 @ (k2_tarski @ X26 @ X28) @ X27) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k2_tarski @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf(t4_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.50  thf(t64_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.50         (((X22) != (X24))
% 0.22/0.50          | ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X24 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.50  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '52'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.22/0.50      inference('clc', [status(thm)], ['49', '53'])).
% 0.22/0.50  thf('55', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '54'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['45', '55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.22/0.50        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.22/0.50        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.22/0.50         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['58', '60'])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['59'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (((sk_D)
% 0.22/0.50         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      ((((sk_D)
% 0.22/0.50          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.50             (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['64', '65'])).
% 0.22/0.50  thf(d3_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.50         ((k3_mcart_1 @ X30 @ X31 @ X32)
% 0.22/0.50           = (k4_tarski @ (k4_tarski @ X30 @ X31) @ X32))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.50  thf(t20_mcart_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.50         (((X36) != (k2_mcart_1 @ X36)) | ((X36) != (k4_tarski @ X37 @ X38)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i]:
% 0.22/0.50         ((k4_tarski @ X37 @ X38) != (k2_mcart_1 @ (k4_tarski @ X37 @ X38)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['68'])).
% 0.22/0.50  thf(t7_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (![X51 : $i, X53 : $i]: ((k2_mcart_1 @ (k4_tarski @ X51 @ X53)) = (X53))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('71', plain, (![X37 : $i, X38 : $i]: ((k4_tarski @ X37 @ X38) != (X38))),
% 0.22/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['67', '71'])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['66', '72'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.50         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['59'])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      ((((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.22/0.50         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (((sk_D)
% 0.22/0.50         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.50          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '41'])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.50         (((X39) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X40 @ X39)
% 0.22/0.50          | ((sk_B @ X39) != (k3_mcart_1 @ X41 @ X40 @ X42)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))
% 0.22/0.50          | ((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['80'])).
% 0.22/0.50  thf('82', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '54'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      (~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['77', '83'])).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))
% 0.22/0.50         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['76', '84'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         (((X15) != (X14))
% 0.22/0.50          | (r2_hidden @ X15 @ X16)
% 0.22/0.50          | ((X16) != (k1_tarski @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('87', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.22/0.50      inference('simplify', [status(thm)], ['86'])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      (~ (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['85', '87'])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.22/0.50       (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.22/0.50       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['59'])).
% 0.22/0.50  thf('90', plain, ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['73', '88', '89'])).
% 0.22/0.50  thf('91', plain, (((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['61', '90'])).
% 0.22/0.50  thf('92', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.22/0.50      inference('simplify', [status(thm)], ['86'])).
% 0.22/0.50  thf('93', plain, ($false),
% 0.22/0.50      inference('demod', [status(thm)], ['57', '91', '92'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
