%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d6OGqvD56Y

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  172 (2069 expanded)
%              Number of leaves         :   32 ( 615 expanded)
%              Depth                    :   21
%              Number of atoms          : 1751 (44956 expanded)
%              Number of equality atoms :  267 (7369 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X38 @ X39 @ X41 @ X40 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k3_zfmisc_1 @ X38 @ X39 @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X37
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X34 @ X35 @ X36 @ X37 ) @ ( k6_mcart_1 @ X34 @ X35 @ X36 @ X37 ) @ ( k7_mcart_1 @ X34 @ X35 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X34 @ X35 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X38 @ X39 @ X41 @ X40 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k3_zfmisc_1 @ X38 @ X39 @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X38 @ X39 @ X41 @ X40 )
        = ( k2_mcart_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k3_zfmisc_1 @ X38 @ X39 @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','28','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['17','40'])).

thf('42',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k3_mcart_1 @ X32 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_1 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_1 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','43'])).

thf('45',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf('46',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('50',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('51',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39'])).

thf('53',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
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

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k2_mcart_1 @ X27 ) )
      | ( X27
       != ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_tarski @ X28 @ X29 )
     != ( k2_mcart_1 @ ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('57',plain,(
    ! [X42: $i,X44: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X42 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_tarski @ X28 @ X29 )
     != X29 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( X1
        = ( sk_B @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('74',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('75',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39'])).

thf('77',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k3_mcart_1 @ X32 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('83',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
          = X0 )
        | ( r2_hidden @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('88',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('92',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_1 ) )
         != sk_D_1 )
        | ( ( k2_tarski @ X0 @ sk_D_1 )
          = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_1 )
        | ( X0 = sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_D_1 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_D_1 )
        = sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39'])).

thf('102',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_mcart_1 @ X27 ) )
      | ( X27
       != ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('104',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_tarski @ X28 @ X29 )
     != ( k1_mcart_1 @ ( k4_tarski @ X28 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X42 @ X43 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('106',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_tarski @ X28 @ X29 )
     != X28 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    sk_D_1
 != ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38','39'])).

thf('110',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('111',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X42 @ X43 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_mcart_1 @ sk_D_1 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    sk_D_1
 != ( k1_mcart_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('116',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('117',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X11 ) )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_1 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k2_tarski @ sk_D_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('123',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['100','114','123'])).

thf('125',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('126',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['60','124','125'])).

thf('127',plain,(
    r2_hidden @ sk_D_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('131',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_1 )
        | ( X0 = sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_D_1 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['60','124','125'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_mcart_1 @ sk_D_1 )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    sk_D_1
 != ( k1_mcart_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('138',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d6OGqvD56Y
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.46/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.62  % Solved by: fo/fo7.sh
% 0.46/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.62  % done 275 iterations in 0.170s
% 0.46/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.62  % SZS output start Refutation
% 0.46/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.62  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.62  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.46/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.62  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.62  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.62  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.62  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.46/0.62  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.62  thf(t29_mcart_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ![B:$i]:
% 0.46/0.62            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.62                 ( ![C:$i,D:$i,E:$i]:
% 0.46/0.62                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.62                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.62  thf('0', plain,
% 0.46/0.62      (![X30 : $i]:
% 0.46/0.62         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.46/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.62  thf(d2_tarski, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.62       ( ![D:$i]:
% 0.46/0.62         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.62  thf('1', plain,
% 0.46/0.62      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.62          | ((X4) = (X3))
% 0.46/0.62          | ((X4) = (X0))
% 0.46/0.62          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.62  thf('2', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.46/0.62         (((X4) = (X0))
% 0.46/0.62          | ((X4) = (X3))
% 0.46/0.62          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.62  thf('3', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.62          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.46/0.62          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.62  thf('4', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (((X0) != (X1))
% 0.46/0.62          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.46/0.62          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.62      inference('eq_fact', [status(thm)], ['3'])).
% 0.46/0.62  thf('5', plain,
% 0.46/0.62      (![X1 : $i]:
% 0.46/0.62         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.46/0.62          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.62  thf('6', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.62         (((X1) != (X0))
% 0.46/0.62          | (r2_hidden @ X1 @ X2)
% 0.46/0.62          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.62  thf('7', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.62  thf(t51_mcart_1, conjecture,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ~( ![D:$i]:
% 0.46/0.62               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.62                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.62                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.62                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.62        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62             ( ~( ![D:$i]:
% 0.46/0.62                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.62                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.62                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.46/0.62                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.46/0.62    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.46/0.62  thf('8', plain,
% 0.46/0.62      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(t50_mcart_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ~( ![D:$i]:
% 0.46/0.62               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.62                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.46/0.62                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.46/0.62                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.46/0.62                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.46/0.62                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.46/0.62  thf('9', plain,
% 0.46/0.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.62         (((X38) = (k1_xboole_0))
% 0.46/0.62          | ((X39) = (k1_xboole_0))
% 0.46/0.62          | ((k5_mcart_1 @ X38 @ X39 @ X41 @ X40)
% 0.46/0.62              = (k1_mcart_1 @ (k1_mcart_1 @ X40)))
% 0.46/0.62          | ~ (m1_subset_1 @ X40 @ (k3_zfmisc_1 @ X38 @ X39 @ X41))
% 0.46/0.62          | ((X41) = (k1_xboole_0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.62  thf('10', plain,
% 0.46/0.62      ((((sk_C) = (k1_xboole_0))
% 0.46/0.62        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.46/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.62  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('14', plain,
% 0.46/0.62      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.46/0.62  thf('15', plain,
% 0.46/0.62      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.46/0.62        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.46/0.62        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('16', plain,
% 0.46/0.62      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('split', [status(esa)], ['15'])).
% 0.46/0.62  thf('17', plain,
% 0.46/0.62      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['14', '16'])).
% 0.46/0.62  thf('18', plain,
% 0.46/0.62      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(t48_mcart_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.62          ( ~( ![D:$i]:
% 0.46/0.62               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.46/0.62                 ( ( D ) =
% 0.46/0.62                   ( k3_mcart_1 @
% 0.46/0.62                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.46/0.62                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.46/0.62                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.62  thf('19', plain,
% 0.46/0.62      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.62         (((X34) = (k1_xboole_0))
% 0.46/0.62          | ((X35) = (k1_xboole_0))
% 0.46/0.62          | ((X37)
% 0.46/0.62              = (k3_mcart_1 @ (k5_mcart_1 @ X34 @ X35 @ X36 @ X37) @ 
% 0.46/0.62                 (k6_mcart_1 @ X34 @ X35 @ X36 @ X37) @ 
% 0.46/0.62                 (k7_mcart_1 @ X34 @ X35 @ X36 @ X37)))
% 0.46/0.62          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X34 @ X35 @ X36))
% 0.46/0.62          | ((X36) = (k1_xboole_0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.46/0.62  thf('20', plain,
% 0.46/0.62      ((((sk_C) = (k1_xboole_0))
% 0.46/0.62        | ((sk_D_1)
% 0.46/0.62            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.46/0.62               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.46/0.62               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.46/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.62  thf('21', plain,
% 0.46/0.62      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.46/0.62  thf('22', plain,
% 0.46/0.62      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('23', plain,
% 0.46/0.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.62         (((X38) = (k1_xboole_0))
% 0.46/0.62          | ((X39) = (k1_xboole_0))
% 0.46/0.62          | ((k6_mcart_1 @ X38 @ X39 @ X41 @ X40)
% 0.46/0.62              = (k2_mcart_1 @ (k1_mcart_1 @ X40)))
% 0.46/0.62          | ~ (m1_subset_1 @ X40 @ (k3_zfmisc_1 @ X38 @ X39 @ X41))
% 0.46/0.62          | ((X41) = (k1_xboole_0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.62  thf('24', plain,
% 0.46/0.62      ((((sk_C) = (k1_xboole_0))
% 0.46/0.62        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.46/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('26', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('28', plain,
% 0.46/0.62      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.46/0.62  thf('29', plain,
% 0.46/0.62      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('30', plain,
% 0.46/0.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.62         (((X38) = (k1_xboole_0))
% 0.46/0.62          | ((X39) = (k1_xboole_0))
% 0.46/0.62          | ((k7_mcart_1 @ X38 @ X39 @ X41 @ X40) = (k2_mcart_1 @ X40))
% 0.46/0.62          | ~ (m1_subset_1 @ X40 @ (k3_zfmisc_1 @ X38 @ X39 @ X41))
% 0.46/0.62          | ((X41) = (k1_xboole_0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.46/0.62  thf('31', plain,
% 0.46/0.62      ((((sk_C) = (k1_xboole_0))
% 0.46/0.62        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))
% 0.46/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.62  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('35', plain,
% 0.46/0.62      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.46/0.62  thf('36', plain,
% 0.46/0.62      ((((sk_C) = (k1_xboole_0))
% 0.46/0.62        | ((sk_D_1)
% 0.46/0.62            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.46/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.62      inference('demod', [status(thm)], ['20', '21', '28', '35'])).
% 0.46/0.62  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('40', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37', '38', '39'])).
% 0.46/0.62  thf('41', plain,
% 0.46/0.62      ((((sk_D_1)
% 0.46/0.62          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62             (k2_mcart_1 @ sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['17', '40'])).
% 0.46/0.62  thf('42', plain,
% 0.46/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.62         (((X30) = (k1_xboole_0))
% 0.46/0.62          | ~ (r2_hidden @ X32 @ X30)
% 0.46/0.62          | ((sk_B @ X30) != (k3_mcart_1 @ X32 @ X31 @ X33)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.62  thf('43', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((sk_B @ X0) != (sk_D_1))
% 0.46/0.62           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.46/0.62           | ((X0) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.62  thf('44', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((k2_tarski @ X0 @ sk_D_1) = (k1_xboole_0))
% 0.46/0.62           | ((sk_B @ (k2_tarski @ X0 @ sk_D_1)) != (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['7', '43'])).
% 0.46/0.62  thf('45', plain,
% 0.46/0.62      (((((sk_D_1) != (sk_D_1))
% 0.46/0.62         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))
% 0.46/0.62         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['5', '44'])).
% 0.46/0.62  thf('46', plain,
% 0.46/0.62      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.62  thf('47', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.62  thf('48', plain,
% 0.46/0.62      (((r2_hidden @ sk_D_1 @ k1_xboole_0))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.62  thf('49', plain,
% 0.46/0.62      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.46/0.62  thf('50', plain,
% 0.46/0.62      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('split', [status(esa)], ['15'])).
% 0.46/0.62  thf('51', plain,
% 0.46/0.62      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.62  thf('52', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37', '38', '39'])).
% 0.46/0.62  thf('53', plain,
% 0.46/0.62      ((((sk_D_1)
% 0.46/0.62          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.62  thf(d3_mcart_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.46/0.62  thf('54', plain,
% 0.46/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.62         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.46/0.62           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.46/0.62  thf(t20_mcart_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.62       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.46/0.62  thf('55', plain,
% 0.46/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.62         (((X27) != (k2_mcart_1 @ X27)) | ((X27) != (k4_tarski @ X28 @ X29)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.46/0.62  thf('56', plain,
% 0.46/0.62      (![X28 : $i, X29 : $i]:
% 0.46/0.62         ((k4_tarski @ X28 @ X29) != (k2_mcart_1 @ (k4_tarski @ X28 @ X29)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.62  thf(t7_mcart_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.46/0.62       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.46/0.62  thf('57', plain,
% 0.46/0.62      (![X42 : $i, X44 : $i]: ((k2_mcart_1 @ (k4_tarski @ X42 @ X44)) = (X44))),
% 0.46/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.62  thf('58', plain, (![X28 : $i, X29 : $i]: ((k4_tarski @ X28 @ X29) != (X29))),
% 0.46/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.62  thf('59', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['54', '58'])).
% 0.46/0.62  thf('60', plain,
% 0.46/0.62      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['53', '59'])).
% 0.46/0.62  thf('61', plain,
% 0.46/0.62      (![X30 : $i]:
% 0.46/0.62         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.46/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.62  thf(t65_zfmisc_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.46/0.62       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.62  thf('62', plain,
% 0.46/0.62      (![X12 : $i, X13 : $i]:
% 0.46/0.62         (((k4_xboole_0 @ X12 @ (k1_tarski @ X13)) = (X12))
% 0.46/0.62          | (r2_hidden @ X13 @ X12))),
% 0.46/0.62      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.62  thf(t72_zfmisc_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.62       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.46/0.62  thf('63', plain,
% 0.46/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X14 @ X15)
% 0.46/0.62          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 0.46/0.62              != (k2_tarski @ X14 @ X16)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.46/0.62  thf('64', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.46/0.62          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.62          | ~ (r2_hidden @ X1 @ (k1_tarski @ X2)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.62  thf('65', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X1 @ (k1_tarski @ X2))
% 0.46/0.62          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.62  thf('66', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.62          | (r2_hidden @ X0 @ (k2_tarski @ (sk_B @ (k1_tarski @ X0)) @ X1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['61', '65'])).
% 0.46/0.62  thf('67', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.46/0.62         (((X4) = (X0))
% 0.46/0.62          | ((X4) = (X3))
% 0.46/0.62          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.62  thf('68', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.46/0.62          | ((X1) = (sk_B @ (k1_tarski @ X1)))
% 0.46/0.62          | ((X1) = (X0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.62  thf('69', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.62          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.46/0.62      inference('condensation', [status(thm)], ['68'])).
% 0.46/0.62  thf('70', plain,
% 0.46/0.62      (![X30 : $i]:
% 0.46/0.62         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.46/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.62  thf('71', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.46/0.62          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.62  thf('72', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.62          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['71'])).
% 0.46/0.62  thf('73', plain,
% 0.46/0.62      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.46/0.62         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.46/0.62  thf('74', plain,
% 0.46/0.62      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('split', [status(esa)], ['15'])).
% 0.46/0.62  thf('75', plain,
% 0.46/0.62      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.62  thf('76', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37', '38', '39'])).
% 0.46/0.62  thf('77', plain,
% 0.46/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.62         (((X30) = (k1_xboole_0))
% 0.46/0.62          | ~ (r2_hidden @ X31 @ X30)
% 0.46/0.62          | ((sk_B @ X30) != (k3_mcart_1 @ X32 @ X31 @ X33)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.46/0.62  thf('78', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (((sk_B @ X0) != (sk_D_1))
% 0.46/0.62          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ X0)
% 0.46/0.62          | ((X0) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.62  thf('79', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.46/0.62           | ((X0) = (k1_xboole_0))
% 0.46/0.62           | ((sk_B @ X0) != (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['75', '78'])).
% 0.46/0.62  thf('80', plain,
% 0.46/0.62      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.46/0.62         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.46/0.62         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['72', '79'])).
% 0.46/0.62  thf('81', plain,
% 0.46/0.62      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.46/0.62         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.46/0.62  thf('82', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.62          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.46/0.62      inference('condensation', [status(thm)], ['68'])).
% 0.46/0.62  thf('83', plain,
% 0.46/0.62      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('clc', [status(thm)], ['81', '82'])).
% 0.46/0.62  thf('84', plain,
% 0.46/0.62      (![X12 : $i, X13 : $i]:
% 0.46/0.62         (((k4_xboole_0 @ X12 @ (k1_tarski @ X13)) = (X12))
% 0.46/0.62          | (r2_hidden @ X13 @ X12))),
% 0.46/0.62      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.62  thf('85', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.46/0.62           | (r2_hidden @ sk_D_1 @ X0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['83', '84'])).
% 0.46/0.62  thf(t113_zfmisc_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.62  thf('86', plain,
% 0.46/0.62      (![X9 : $i, X10 : $i]:
% 0.46/0.62         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.62  thf('87', plain,
% 0.46/0.62      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.62  thf(t10_mcart_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.46/0.62       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.46/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.46/0.62  thf('88', plain,
% 0.46/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.62         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.46/0.62          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.62  thf('89', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.46/0.62          | (r2_hidden @ (k1_mcart_1 @ X1) @ X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.62  thf('90', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.62           | (r2_hidden @ (k1_mcart_1 @ sk_D_1) @ X0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['85', '89'])).
% 0.46/0.62  thf('91', plain,
% 0.46/0.62      (![X1 : $i]:
% 0.46/0.62         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.46/0.62          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.62  thf('92', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.62  thf('93', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.46/0.62           | ((X0) = (k1_xboole_0))
% 0.46/0.62           | ((sk_B @ X0) != (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['75', '78'])).
% 0.46/0.62  thf('94', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((sk_B @ (k2_tarski @ X0 @ sk_D_1)) != (sk_D_1))
% 0.46/0.62           | ((k2_tarski @ X0 @ sk_D_1) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.62  thf('95', plain,
% 0.46/0.62      (((((sk_D_1) != (sk_D_1))
% 0.46/0.62         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))
% 0.46/0.62         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['91', '94'])).
% 0.46/0.62  thf('96', plain,
% 0.46/0.62      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.62  thf('97', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.46/0.62         (((X4) = (X0))
% 0.46/0.62          | ((X4) = (X3))
% 0.46/0.62          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.62  thf('98', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.62           | ((X0) = (sk_D_1))
% 0.46/0.62           | ((X0) = (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.62  thf('99', plain,
% 0.46/0.62      ((![X0 : $i]: (((X0) = (sk_D_1)) | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.62  thf('100', plain,
% 0.46/0.62      (((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.62         | ((k1_mcart_1 @ sk_D_1) = (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['90', '99'])).
% 0.46/0.62  thf('101', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37', '38', '39'])).
% 0.46/0.62  thf('102', plain,
% 0.46/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.62         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.46/0.62           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.46/0.62  thf('103', plain,
% 0.46/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.62         (((X27) != (k1_mcart_1 @ X27)) | ((X27) != (k4_tarski @ X28 @ X29)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.46/0.62  thf('104', plain,
% 0.46/0.62      (![X28 : $i, X29 : $i]:
% 0.46/0.62         ((k4_tarski @ X28 @ X29) != (k1_mcart_1 @ (k4_tarski @ X28 @ X29)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.62  thf('105', plain,
% 0.46/0.62      (![X42 : $i, X43 : $i]: ((k1_mcart_1 @ (k4_tarski @ X42 @ X43)) = (X42))),
% 0.46/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.62  thf('106', plain,
% 0.46/0.62      (![X28 : $i, X29 : $i]: ((k4_tarski @ X28 @ X29) != (X28))),
% 0.46/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.62  thf('107', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((k3_mcart_1 @ X2 @ X1 @ X0) != (k4_tarski @ X2 @ X1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['102', '106'])).
% 0.46/0.62  thf('108', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         != (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['101', '107'])).
% 0.46/0.62  thf('109', plain,
% 0.46/0.62      (((sk_D_1)
% 0.46/0.62         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37', '38', '39'])).
% 0.46/0.62  thf('110', plain,
% 0.46/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.62         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.46/0.62           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.46/0.62  thf('111', plain,
% 0.46/0.62      (![X42 : $i, X43 : $i]: ((k1_mcart_1 @ (k4_tarski @ X42 @ X43)) = (X42))),
% 0.46/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.62  thf('112', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.46/0.62      inference('sup+', [status(thm)], ['110', '111'])).
% 0.46/0.62  thf('113', plain,
% 0.46/0.62      (((k1_mcart_1 @ sk_D_1)
% 0.46/0.62         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.46/0.62            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))),
% 0.46/0.62      inference('sup+', [status(thm)], ['109', '112'])).
% 0.46/0.62  thf('114', plain, (((sk_D_1) != (k1_mcart_1 @ sk_D_1))),
% 0.46/0.62      inference('demod', [status(thm)], ['108', '113'])).
% 0.46/0.62  thf('115', plain,
% 0.46/0.62      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.62  thf('116', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.62  thf('117', plain,
% 0.46/0.62      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('clc', [status(thm)], ['81', '82'])).
% 0.46/0.62  thf('118', plain,
% 0.46/0.62      (![X11 : $i, X12 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X11 @ X12)
% 0.46/0.62          | ((k4_xboole_0 @ X12 @ (k1_tarski @ X11)) != (X12)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.62  thf('119', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.46/0.62           | ~ (r2_hidden @ sk_D_1 @ X0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.62  thf('120', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.46/0.62            != (k2_tarski @ X0 @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['116', '119'])).
% 0.46/0.62  thf('121', plain,
% 0.46/0.62      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.62          != (k2_tarski @ sk_D_1 @ sk_D_1)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['115', '120'])).
% 0.46/0.62  thf('122', plain,
% 0.46/0.62      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.62  thf('123', plain,
% 0.46/0.62      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('demod', [status(thm)], ['121', '122'])).
% 0.46/0.62  thf('124', plain,
% 0.46/0.62      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['100', '114', '123'])).
% 0.46/0.62  thf('125', plain,
% 0.46/0.62      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.46/0.62       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.46/0.62       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('split', [status(esa)], ['15'])).
% 0.46/0.62  thf('126', plain,
% 0.46/0.62      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('sat_resolution*', [status(thm)], ['60', '124', '125'])).
% 0.46/0.62  thf('127', plain, ((r2_hidden @ sk_D_1 @ k1_xboole_0)),
% 0.46/0.62      inference('simpl_trail', [status(thm)], ['48', '126'])).
% 0.46/0.62  thf('128', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.46/0.62          | (r2_hidden @ (k1_mcart_1 @ X1) @ X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.62  thf('129', plain, (![X0 : $i]: (r2_hidden @ (k1_mcart_1 @ sk_D_1) @ X0)),
% 0.46/0.62      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.62  thf('130', plain,
% 0.46/0.62      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.62  thf('131', plain,
% 0.46/0.62      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.46/0.62         (((X4) = (X0))
% 0.46/0.62          | ((X4) = (X3))
% 0.46/0.62          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.62  thf('132', plain,
% 0.46/0.62      ((![X0 : $i]:
% 0.46/0.62          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.62           | ((X0) = (sk_D_1))
% 0.46/0.62           | ((X0) = (sk_D_1))))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.62  thf('133', plain,
% 0.46/0.62      ((![X0 : $i]: (((X0) = (sk_D_1)) | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 0.46/0.62         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.46/0.62      inference('simplify', [status(thm)], ['132'])).
% 0.46/0.62  thf('134', plain,
% 0.46/0.62      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.46/0.62      inference('sat_resolution*', [status(thm)], ['60', '124', '125'])).
% 0.46/0.62  thf('135', plain,
% 0.46/0.62      (![X0 : $i]: (((X0) = (sk_D_1)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.62      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.46/0.62  thf('136', plain, (((k1_mcart_1 @ sk_D_1) = (sk_D_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.62  thf('137', plain, (((sk_D_1) != (k1_mcart_1 @ sk_D_1))),
% 0.46/0.62      inference('demod', [status(thm)], ['108', '113'])).
% 0.46/0.62  thf('138', plain, ($false),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 0.46/0.62  
% 0.46/0.62  % SZS output end Refutation
% 0.46/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
