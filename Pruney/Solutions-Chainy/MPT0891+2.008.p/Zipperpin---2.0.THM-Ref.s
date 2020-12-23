%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mlWYdlgSSY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 492 expanded)
%              Number of leaves         :   34 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          : 1261 (8522 expanded)
%              Number of equality atoms :  185 (1327 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X45
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X42 @ X43 @ X44 @ X45 ) @ ( k6_mcart_1 @ X42 @ X43 @ X44 @ X45 ) @ ( k7_mcart_1 @ X42 @ X43 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X45
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X42 @ X43 @ X44 @ X45 ) @ ( k6_mcart_1 @ X42 @ X43 @ X44 @ X45 ) @ ( k7_mcart_1 @ X42 @ X43 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X46 @ X47 @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X46 @ X47 @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X46 @ X47 @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('41',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
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

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X25 @ X27 ) @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X22 ) )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['46','56'])).

thf('58',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( r2_hidden @ X40 @ X38 )
      | ( ( sk_B @ X38 )
       != ( k3_mcart_1 @ X40 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','62'])).

thf('64',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('65',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('69',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['65'])).

thf('70',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('72',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_mcart_1 @ X29 @ X30 @ X31 )
      = ( k4_tarski @ ( k4_tarski @ X29 @ X30 ) @ X31 ) ) ),
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

thf('74',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k2_mcart_1 @ X35 ) )
      | ( X35
       != ( k4_tarski @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('75',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_tarski @ X36 @ X37 )
     != ( k2_mcart_1 @ ( k4_tarski @ X36 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('76',plain,(
    ! [X50: $i,X52: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X50 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('77',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_tarski @ X36 @ X37 )
     != X37 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['72','78'])).

thf('80',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('81',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['65'])).

thf('82',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['46','56'])).

thf('85',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( r2_hidden @ X39 @ X38 )
      | ( ( sk_B @ X38 )
       != ( k3_mcart_1 @ X40 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('89',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('93',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['91','93'])).

thf('95',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['65'])).

thf('96',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['79','94','95'])).

thf('97',plain,
    ( sk_D
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['67','96'])).

thf('98',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['63','97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mlWYdlgSSY
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 102 iterations in 0.030s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(t51_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.49                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.49                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49             ( ~( ![D:$i]:
% 0.22/0.49                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.49                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.22/0.49                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t48_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                 ( ( D ) =
% 0.22/0.49                   ( k3_mcart_1 @
% 0.22/0.49                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.49                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.22/0.49                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.49         (((X42) = (k1_xboole_0))
% 0.22/0.49          | ((X43) = (k1_xboole_0))
% 0.22/0.49          | ((X45)
% 0.22/0.49              = (k3_mcart_1 @ (k5_mcart_1 @ X42 @ X43 @ X44 @ X45) @ 
% 0.22/0.49                 (k6_mcart_1 @ X42 @ X43 @ X44 @ X45) @ 
% 0.22/0.49                 (k7_mcart_1 @ X42 @ X43 @ X44 @ X45)))
% 0.22/0.49          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X42 @ X43 @ X44))
% 0.22/0.49          | ((X44) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.49         (((X42) = (k1_xboole_0))
% 0.22/0.49          | ((X43) = (k1_xboole_0))
% 0.22/0.49          | ((X45)
% 0.22/0.49              = (k3_mcart_1 @ (k5_mcart_1 @ X42 @ X43 @ X44 @ X45) @ 
% 0.22/0.49                 (k6_mcart_1 @ X42 @ X43 @ X44 @ X45) @ 
% 0.22/0.49                 (k7_mcart_1 @ X42 @ X43 @ X44 @ X45)))
% 0.22/0.49          | ~ (m1_subset_1 @ X45 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43) @ X44))
% 0.22/0.49          | ((X44) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_D)
% 0.22/0.49            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.22/0.49               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.22/0.49               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.49        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t50_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![D:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.49                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.49                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.49                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.49                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k5_mcart_1 @ X46 @ X47 @ X49 @ X48)
% 0.22/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ X48)))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X46 @ X47 @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k5_mcart_1 @ X46 @ X47 @ X49 @ X48)
% 0.22/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ X48)))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.49        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.22/0.49        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.49  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X46 @ X47 @ X49 @ X48)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X48)))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X46 @ X47 @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k6_mcart_1 @ X46 @ X47 @ X49 @ X48)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X48)))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.49        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.22/0.49        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '19'])).
% 0.22/0.49  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k7_mcart_1 @ X46 @ X47 @ X49 @ X48) = (k2_mcart_1 @ X48))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X46 @ X47 @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.22/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         (((X46) = (k1_xboole_0))
% 0.22/0.49          | ((X47) = (k1_xboole_0))
% 0.22/0.49          | ((k7_mcart_1 @ X46 @ X47 @ X49 @ X48) = (k2_mcart_1 @ X48))
% 0.22/0.49          | ~ (m1_subset_1 @ X48 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X49))
% 0.22/0.49          | ((X49) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.49        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.22/0.49        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.49  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_D)
% 0.22/0.49            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.22/0.49        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '15', '24', '33'])).
% 0.22/0.49  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t29_mcart_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.49                 ( ![C:$i,D:$i,E:$i]:
% 0.22/0.49                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.49                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X38 : $i]:
% 0.22/0.49         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.49  thf(d1_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X17 @ X16)
% 0.22/0.49          | ((X17) = (X14))
% 0.22/0.49          | ((X16) != (k1_tarski @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X14 : $i, X17 : $i]:
% 0.22/0.49         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.49          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['40', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['39', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf(t73_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.49         ((r2_hidden @ X25 @ X26)
% 0.22/0.49          | ((k4_xboole_0 @ (k2_tarski @ X25 @ X27) @ X26) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k2_tarski @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.49          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf(t4_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.49  thf(t65_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (![X22 : $i, X23 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.49          | ((k4_xboole_0 @ X23 @ (k1_tarski @ X22)) != (X23)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.49      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('clc', [status(thm)], ['50', '54'])).
% 0.22/0.49  thf('56', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '55'])).
% 0.22/0.49  thf('57', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['46', '56'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.49         (((X38) = (k1_xboole_0))
% 0.22/0.49          | ~ (r2_hidden @ X40 @ X38)
% 0.22/0.49          | ((sk_B @ X38) != (k3_mcart_1 @ X40 @ X39 @ X41)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.22/0.49          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.22/0.49          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.49  thf('61', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '55'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      (~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.22/0.49        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.22/0.49        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      ((((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.22/0.49         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['64', '66'])).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.49  thf('69', plain,
% 0.22/0.49      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['65'])).
% 0.22/0.49  thf('70', plain,
% 0.22/0.49      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['68', '69'])).
% 0.22/0.49  thf('71', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.49  thf('72', plain,
% 0.22/0.49      ((((sk_D)
% 0.22/0.49          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49             (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf(d3_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('73', plain,
% 0.22/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.49         ((k3_mcart_1 @ X29 @ X30 @ X31)
% 0.22/0.49           = (k4_tarski @ (k4_tarski @ X29 @ X30) @ X31))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.49  thf(t20_mcart_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.49       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.49         (((X35) != (k2_mcart_1 @ X35)) | ((X35) != (k4_tarski @ X36 @ X37)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.22/0.49  thf('75', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         ((k4_tarski @ X36 @ X37) != (k2_mcart_1 @ (k4_tarski @ X36 @ X37)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['74'])).
% 0.22/0.49  thf(t7_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.49  thf('76', plain,
% 0.22/0.49      (![X50 : $i, X52 : $i]: ((k2_mcart_1 @ (k4_tarski @ X50 @ X52)) = (X52))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.49  thf('77', plain, (![X36 : $i, X37 : $i]: ((k4_tarski @ X36 @ X37) != (X37))),
% 0.22/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.49  thf('78', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['73', '77'])).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['72', '78'])).
% 0.22/0.49  thf('80', plain,
% 0.22/0.49      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.22/0.49  thf('81', plain,
% 0.22/0.49      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['65'])).
% 0.22/0.49  thf('82', plain,
% 0.22/0.49      ((((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.22/0.49         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['80', '81'])).
% 0.22/0.49  thf('83', plain,
% 0.22/0.49      (((sk_D)
% 0.22/0.49         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.22/0.49            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.49  thf('84', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['46', '56'])).
% 0.22/0.49  thf('85', plain,
% 0.22/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.49         (((X38) = (k1_xboole_0))
% 0.22/0.49          | ~ (r2_hidden @ X39 @ X38)
% 0.22/0.49          | ((sk_B @ X38) != (k3_mcart_1 @ X40 @ X39 @ X41)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.49  thf('86', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['84', '85'])).
% 0.22/0.49  thf('87', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.22/0.49          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['86'])).
% 0.22/0.49  thf('88', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '55'])).
% 0.22/0.49  thf('89', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.22/0.49  thf('90', plain,
% 0.22/0.49      (~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['83', '89'])).
% 0.22/0.49  thf('91', plain,
% 0.22/0.49      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))
% 0.22/0.49         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['82', '90'])).
% 0.22/0.49  thf('92', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (((X15) != (X14))
% 0.22/0.49          | (r2_hidden @ X15 @ X16)
% 0.22/0.49          | ((X16) != (k1_tarski @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('93', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.22/0.49      inference('simplify', [status(thm)], ['92'])).
% 0.22/0.49  thf('94', plain,
% 0.22/0.49      (~ (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.49      inference('demod', [status(thm)], ['91', '93'])).
% 0.22/0.49  thf('95', plain,
% 0.22/0.49      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.22/0.49       (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.22/0.49       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.49      inference('split', [status(esa)], ['65'])).
% 0.22/0.49  thf('96', plain, ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['79', '94', '95'])).
% 0.22/0.49  thf('97', plain, (((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['67', '96'])).
% 0.22/0.49  thf('98', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.22/0.49      inference('simplify', [status(thm)], ['92'])).
% 0.22/0.49  thf('99', plain, ($false),
% 0.22/0.49      inference('demod', [status(thm)], ['63', '97', '98'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
