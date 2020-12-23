%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wwYaZdUIQ9

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:42 EST 2020

% Result     : Theorem 5.56s
% Output     : Refutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 870 expanded)
%              Number of leaves         :   30 ( 273 expanded)
%              Depth                    :   26
%              Number of atoms          : 1647 (9141 expanded)
%              Number of equality atoms :  101 ( 574 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t66_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( r2_relset_1 @ X58 @ X59 @ X60 @ X57 )
      | ( r2_hidden @ ( sk_E @ X57 @ X60 @ X58 ) @ X58 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D_1 @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D_1 @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('18',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ( X63 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X64 @ X61 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

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
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k3_subset_1 @ X50 @ X51 )
        = ( k4_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_subset_1 @ X53 @ ( k3_subset_1 @ X53 @ X52 ) )
        = X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('57',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k3_subset_1 @ X50 @ X51 )
        = ( k4_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','61'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('67',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('72',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ X1 @ X0 @ X1 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['82'])).

thf('84',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['84','88'])).

thf('90',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['89','93'])).

thf('95',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('96',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( r2_relset_1 @ X58 @ X59 @ X60 @ X57 )
      | ( ( k1_funct_1 @ X60 @ ( sk_E @ X57 @ X60 @ X58 ) )
       != ( k1_funct_1 @ X57 @ ( sk_E @ X57 @ X60 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('100',plain,(
    r2_hidden @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['14','15'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ( X63 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X64 @ X61 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('112',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['82'])).

thf('114',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('116',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['92'])).

thf('118',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('120',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['98','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','124'])).

thf('126',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wwYaZdUIQ9
% 0.15/0.37  % Computer   : n024.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:23:51 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 5.56/5.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.56/5.85  % Solved by: fo/fo7.sh
% 5.56/5.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.56/5.85  % done 3440 iterations in 5.362s
% 5.56/5.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.56/5.85  % SZS output start Refutation
% 5.56/5.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.56/5.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.56/5.85  thf(sk_A_type, type, sk_A: $i).
% 5.56/5.85  thf(sk_B_type, type, sk_B: $i).
% 5.56/5.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.56/5.85  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.56/5.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.56/5.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.56/5.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.56/5.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.56/5.85  thf(sk_D_1_type, type, sk_D_1: $i).
% 5.56/5.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.56/5.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.56/5.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.56/5.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.56/5.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.56/5.85  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.56/5.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.56/5.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.56/5.85  thf(t66_funct_2, conjecture,
% 5.56/5.85    (![A:$i,B:$i,C:$i]:
% 5.56/5.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 5.56/5.85         ( m1_subset_1 @
% 5.56/5.85           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 5.56/5.85       ( ![D:$i]:
% 5.56/5.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 5.56/5.85             ( m1_subset_1 @
% 5.56/5.85               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 5.56/5.85           ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ))).
% 5.56/5.85  thf(zf_stmt_0, negated_conjecture,
% 5.56/5.85    (~( ![A:$i,B:$i,C:$i]:
% 5.56/5.85        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 5.56/5.85            ( m1_subset_1 @
% 5.56/5.85              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 5.56/5.85          ( ![D:$i]:
% 5.56/5.85            ( ( ( v1_funct_1 @ D ) & 
% 5.56/5.85                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 5.56/5.85                ( m1_subset_1 @
% 5.56/5.85                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 5.56/5.85              ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ) )),
% 5.56/5.85    inference('cnf.neg', [status(esa)], [t66_funct_2])).
% 5.56/5.85  thf('0', plain,
% 5.56/5.85      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('1', plain,
% 5.56/5.85      ((m1_subset_1 @ sk_D_1 @ 
% 5.56/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf(d1_tarski, axiom,
% 5.56/5.85    (![A:$i,B:$i]:
% 5.56/5.85     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 5.56/5.85       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 5.56/5.85  thf('2', plain,
% 5.56/5.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.56/5.85         (((X14) != (X13))
% 5.56/5.85          | (r2_hidden @ X14 @ X15)
% 5.56/5.85          | ((X15) != (k1_tarski @ X13)))),
% 5.56/5.85      inference('cnf', [status(esa)], [d1_tarski])).
% 5.56/5.85  thf('3', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 5.56/5.85      inference('simplify', [status(thm)], ['2'])).
% 5.56/5.85  thf('4', plain,
% 5.56/5.85      ((m1_subset_1 @ sk_C_1 @ 
% 5.56/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('5', plain,
% 5.56/5.85      ((m1_subset_1 @ sk_D_1 @ 
% 5.56/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf(t18_funct_2, axiom,
% 5.56/5.85    (![A:$i,B:$i,C:$i]:
% 5.56/5.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.56/5.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.56/5.85       ( ![D:$i]:
% 5.56/5.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.56/5.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.56/5.85           ( ( ![E:$i]:
% 5.56/5.85               ( ( r2_hidden @ E @ A ) =>
% 5.56/5.85                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.56/5.85             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.56/5.85  thf('6', plain,
% 5.56/5.85      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 5.56/5.85         (~ (v1_funct_1 @ X57)
% 5.56/5.85          | ~ (v1_funct_2 @ X57 @ X58 @ X59)
% 5.56/5.85          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 5.56/5.85          | (r2_relset_1 @ X58 @ X59 @ X60 @ X57)
% 5.56/5.85          | (r2_hidden @ (sk_E @ X57 @ X60 @ X58) @ X58)
% 5.56/5.85          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 5.56/5.85          | ~ (v1_funct_2 @ X60 @ X58 @ X59)
% 5.56/5.85          | ~ (v1_funct_1 @ X60))),
% 5.56/5.85      inference('cnf', [status(esa)], [t18_funct_2])).
% 5.56/5.85  thf('7', plain,
% 5.56/5.85      (![X0 : $i]:
% 5.56/5.85         (~ (v1_funct_1 @ X0)
% 5.56/5.85          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 5.56/5.85          | ~ (m1_subset_1 @ X0 @ 
% 5.56/5.85               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 5.56/5.85          | (r2_hidden @ (sk_E @ sk_D_1 @ X0 @ sk_A) @ sk_A)
% 5.56/5.85          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D_1)
% 5.56/5.85          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))
% 5.56/5.85          | ~ (v1_funct_1 @ sk_D_1))),
% 5.56/5.85      inference('sup-', [status(thm)], ['5', '6'])).
% 5.56/5.85  thf('8', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('9', plain, ((v1_funct_1 @ sk_D_1)),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('10', plain,
% 5.56/5.85      (![X0 : $i]:
% 5.56/5.85         (~ (v1_funct_1 @ X0)
% 5.56/5.85          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 5.56/5.85          | ~ (m1_subset_1 @ X0 @ 
% 5.56/5.85               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 5.56/5.85          | (r2_hidden @ (sk_E @ sk_D_1 @ X0 @ sk_A) @ sk_A)
% 5.56/5.85          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D_1))),
% 5.56/5.85      inference('demod', [status(thm)], ['7', '8', '9'])).
% 5.56/5.85  thf('11', plain,
% 5.56/5.85      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)
% 5.56/5.85        | (r2_hidden @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A) @ sk_A)
% 5.56/5.85        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 5.56/5.85        | ~ (v1_funct_1 @ sk_C_1))),
% 5.56/5.85      inference('sup-', [status(thm)], ['4', '10'])).
% 5.56/5.85  thf('12', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('14', plain,
% 5.56/5.85      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)
% 5.56/5.85        | (r2_hidden @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A) @ sk_A))),
% 5.56/5.85      inference('demod', [status(thm)], ['11', '12', '13'])).
% 5.56/5.85  thf('15', plain,
% 5.56/5.85      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('16', plain, ((r2_hidden @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A) @ sk_A)),
% 5.56/5.85      inference('clc', [status(thm)], ['14', '15'])).
% 5.56/5.85  thf('17', plain,
% 5.56/5.85      ((m1_subset_1 @ sk_D_1 @ 
% 5.56/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf(t7_funct_2, axiom,
% 5.56/5.85    (![A:$i,B:$i,C:$i,D:$i]:
% 5.56/5.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.56/5.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.56/5.85       ( ( r2_hidden @ C @ A ) =>
% 5.56/5.85         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.56/5.85           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 5.56/5.85  thf('18', plain,
% 5.56/5.85      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 5.56/5.85         (~ (r2_hidden @ X61 @ X62)
% 5.56/5.85          | ((X63) = (k1_xboole_0))
% 5.56/5.85          | ~ (v1_funct_1 @ X64)
% 5.56/5.85          | ~ (v1_funct_2 @ X64 @ X62 @ X63)
% 5.56/5.85          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 5.56/5.85          | (r2_hidden @ (k1_funct_1 @ X64 @ X61) @ X63))),
% 5.56/5.85      inference('cnf', [status(esa)], [t7_funct_2])).
% 5.56/5.85  thf('19', plain,
% 5.56/5.85      (![X0 : $i]:
% 5.56/5.85         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 5.56/5.85          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))
% 5.56/5.85          | ~ (v1_funct_1 @ sk_D_1)
% 5.56/5.85          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.56/5.85          | ~ (r2_hidden @ X0 @ sk_A))),
% 5.56/5.85      inference('sup-', [status(thm)], ['17', '18'])).
% 5.56/5.85  thf('20', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 5.56/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.56/5.85  thf('22', plain,
% 5.56/5.85      (![X0 : $i]:
% 5.56/5.85         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 5.56/5.85          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.56/5.85          | ~ (r2_hidden @ X0 @ sk_A))),
% 5.56/5.85      inference('demod', [status(thm)], ['19', '20', '21'])).
% 5.56/5.85  thf('23', plain,
% 5.56/5.85      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.56/5.85        | (r2_hidden @ 
% 5.56/5.85           (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)) @ 
% 5.56/5.85           (k1_tarski @ sk_B)))),
% 5.56/5.85      inference('sup-', [status(thm)], ['16', '22'])).
% 5.56/5.85  thf(d5_xboole_0, axiom,
% 5.56/5.85    (![A:$i,B:$i,C:$i]:
% 5.56/5.85     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.56/5.85       ( ![D:$i]:
% 5.56/5.85         ( ( r2_hidden @ D @ C ) <=>
% 5.56/5.85           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.56/5.85  thf('24', plain,
% 5.56/5.85      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.56/5.85         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 5.56/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.56/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.56/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.85  thf('25', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.56/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.56/5.85      inference('eq_fact', [status(thm)], ['24'])).
% 5.56/5.85  thf('26', plain,
% 5.56/5.85      (![X13 : $i, X15 : $i, X16 : $i]:
% 5.56/5.85         (~ (r2_hidden @ X16 @ X15)
% 5.56/5.85          | ((X16) = (X13))
% 5.56/5.85          | ((X15) != (k1_tarski @ X13)))),
% 5.56/5.85      inference('cnf', [status(esa)], [d1_tarski])).
% 5.56/5.85  thf('27', plain,
% 5.56/5.85      (![X13 : $i, X16 : $i]:
% 5.56/5.85         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 5.56/5.85      inference('simplify', [status(thm)], ['26'])).
% 5.56/5.85  thf('28', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.56/5.85          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.56/5.85      inference('sup-', [status(thm)], ['25', '27'])).
% 5.56/5.85  thf('29', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.56/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.56/5.85      inference('eq_fact', [status(thm)], ['24'])).
% 5.56/5.85  thf('30', plain,
% 5.56/5.85      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.56/5.85         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 5.56/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 5.56/5.85          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.56/5.85          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.56/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.85  thf('31', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 5.56/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.56/5.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 5.56/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.56/5.85      inference('sup-', [status(thm)], ['29', '30'])).
% 5.56/5.85  thf('32', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 5.56/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.56/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.56/5.85      inference('simplify', [status(thm)], ['31'])).
% 5.56/5.85  thf('33', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.56/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.56/5.85      inference('eq_fact', [status(thm)], ['24'])).
% 5.56/5.85  thf('34', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 5.56/5.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 5.56/5.85      inference('clc', [status(thm)], ['32', '33'])).
% 5.56/5.85  thf('35', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         ((r2_hidden @ X0 @ X1)
% 5.56/5.85          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.56/5.85          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.56/5.85      inference('sup+', [status(thm)], ['28', '34'])).
% 5.56/5.85  thf('36', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i]:
% 5.56/5.85         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.56/5.85          | (r2_hidden @ X0 @ X1))),
% 5.56/5.85      inference('simplify', [status(thm)], ['35'])).
% 5.56/5.85  thf('37', plain,
% 5.56/5.85      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.56/5.85         (~ (r2_hidden @ X4 @ X3)
% 5.56/5.85          | ~ (r2_hidden @ X4 @ X2)
% 5.56/5.85          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 5.56/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.56/5.85  thf('38', plain,
% 5.56/5.85      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.56/5.85         (~ (r2_hidden @ X4 @ X2)
% 5.56/5.85          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 5.56/5.85      inference('simplify', [status(thm)], ['37'])).
% 5.56/5.85  thf('39', plain,
% 5.56/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.56/5.85         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 5.56/5.85          | (r2_hidden @ X0 @ X1)
% 5.56/5.85          | ~ (r2_hidden @ X2 @ X1))),
% 5.56/5.85      inference('sup-', [status(thm)], ['36', '38'])).
% 5.56/5.85  thf('40', plain,
% 5.56/5.85      (![X0 : $i]:
% 5.68/5.85         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ 
% 5.68/5.85               (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)) @ X0)
% 5.68/5.85          | (r2_hidden @ sk_B @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['23', '39'])).
% 5.68/5.85  thf('41', plain,
% 5.68/5.85      (((r2_hidden @ sk_B @ 
% 5.68/5.85         (k1_tarski @ (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['3', '40'])).
% 5.68/5.85  thf('42', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.68/5.85         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 5.68/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.68/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.68/5.85  thf('43', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.68/5.85         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 5.68/5.85          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 5.68/5.85          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.68/5.85  thf('44', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.68/5.85          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 5.68/5.85          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.68/5.85          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['42', '43'])).
% 5.68/5.85  thf(d10_xboole_0, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.68/5.85  thf('45', plain,
% 5.68/5.85      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.68/5.85  thf('46', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 5.68/5.85      inference('simplify', [status(thm)], ['45'])).
% 5.68/5.85  thf(t3_subset, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.68/5.85  thf('47', plain,
% 5.68/5.85      (![X54 : $i, X56 : $i]:
% 5.68/5.85         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_subset])).
% 5.68/5.85  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['46', '47'])).
% 5.68/5.85  thf(d5_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.68/5.85  thf('49', plain,
% 5.68/5.85      (![X50 : $i, X51 : $i]:
% 5.68/5.85         (((k3_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))
% 5.68/5.85          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X50)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.68/5.85  thf('50', plain,
% 5.68/5.85      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['48', '49'])).
% 5.68/5.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.68/5.85  thf('51', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 5.68/5.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.68/5.85  thf('52', plain,
% 5.68/5.85      (![X54 : $i, X56 : $i]:
% 5.68/5.85         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_subset])).
% 5.68/5.85  thf('53', plain,
% 5.68/5.85      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['51', '52'])).
% 5.68/5.85  thf(involutiveness_k3_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 5.68/5.85  thf('54', plain,
% 5.68/5.85      (![X52 : $i, X53 : $i]:
% 5.68/5.85         (((k3_subset_1 @ X53 @ (k3_subset_1 @ X53 @ X52)) = (X52))
% 5.68/5.85          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 5.68/5.85      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 5.68/5.85  thf('55', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['53', '54'])).
% 5.68/5.85  thf('56', plain,
% 5.68/5.85      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['51', '52'])).
% 5.68/5.85  thf('57', plain,
% 5.68/5.85      (![X50 : $i, X51 : $i]:
% 5.68/5.85         (((k3_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))
% 5.68/5.85          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X50)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.68/5.85  thf('58', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['56', '57'])).
% 5.68/5.85  thf(t3_boole, axiom,
% 5.68/5.85    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.68/5.85  thf('59', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_boole])).
% 5.68/5.85  thf('60', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 5.68/5.85      inference('sup+', [status(thm)], ['58', '59'])).
% 5.68/5.85  thf('61', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 5.68/5.85      inference('demod', [status(thm)], ['55', '60'])).
% 5.68/5.85  thf('62', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['50', '61'])).
% 5.68/5.85  thf('63', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['50', '61'])).
% 5.68/5.85  thf('64', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.68/5.85          | ((X1) = (k1_xboole_0))
% 5.68/5.85          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.68/5.85          | ((X1) = (k1_xboole_0)))),
% 5.68/5.85      inference('demod', [status(thm)], ['44', '62', '63'])).
% 5.68/5.85  thf('65', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['64'])).
% 5.68/5.85  thf('66', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X4 @ X3)
% 5.68/5.85          | (r2_hidden @ X4 @ X1)
% 5.68/5.85          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.68/5.85  thf('67', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.68/5.85         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['66'])).
% 5.68/5.85  thf('68', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.68/5.85          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 5.68/5.85      inference('sup-', [status(thm)], ['65', '67'])).
% 5.68/5.85  thf('69', plain,
% 5.68/5.85      (![X13 : $i, X16 : $i]:
% 5.68/5.85         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['26'])).
% 5.68/5.85  thf('70', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 5.68/5.85          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ X1) = (X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['68', '69'])).
% 5.68/5.85  thf('71', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['64'])).
% 5.68/5.85  thf('72', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X4 @ X2)
% 5.68/5.85          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['37'])).
% 5.68/5.85  thf('73', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['71', '72'])).
% 5.68/5.85  thf('74', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X0 @ X1)
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['70', '73'])).
% 5.68/5.85  thf('75', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ X0 @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['74'])).
% 5.68/5.85  thf('76', plain,
% 5.68/5.85      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 5.68/5.85            (k1_tarski @ 
% 5.68/5.85             (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85            = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['41', '75'])).
% 5.68/5.85  thf('77', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.68/5.85          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['25', '27'])).
% 5.68/5.85  thf('78', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 5.68/5.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 5.68/5.85      inference('clc', [status(thm)], ['32', '33'])).
% 5.68/5.85  thf('79', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ X0 @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['74'])).
% 5.68/5.85  thf('80', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ (sk_D @ X1 @ X0 @ X1)) @ X0)
% 5.68/5.85              = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['78', '79'])).
% 5.68/5.85  thf('81', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.68/5.85          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.68/5.85          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.68/5.85      inference('sup+', [status(thm)], ['77', '80'])).
% 5.68/5.85  thf('82', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['81'])).
% 5.68/5.85  thf('83', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k1_tarski @ X0) != (k1_xboole_0))
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 5.68/5.85      inference('eq_fact', [status(thm)], ['82'])).
% 5.68/5.85  thf('84', plain,
% 5.68/5.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 5.68/5.85         (k1_tarski @ (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85         = (k1_xboole_0))),
% 5.68/5.85      inference('clc', [status(thm)], ['76', '83'])).
% 5.68/5.85  thf('85', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 5.68/5.85      inference('simplify', [status(thm)], ['2'])).
% 5.68/5.85  thf('86', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X0 @ X1)
% 5.68/5.85          | (r2_hidden @ X0 @ X2)
% 5.68/5.85          | (r2_hidden @ X0 @ X3)
% 5.68/5.85          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.68/5.85  thf('87', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 5.68/5.85          | (r2_hidden @ X0 @ X2)
% 5.68/5.85          | ~ (r2_hidden @ X0 @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['86'])).
% 5.68/5.85  thf('88', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((r2_hidden @ X0 @ X1)
% 5.68/5.85          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['85', '87'])).
% 5.68/5.85  thf('89', plain,
% 5.68/5.85      (((r2_hidden @ sk_B @ k1_xboole_0)
% 5.68/5.85        | (r2_hidden @ sk_B @ 
% 5.68/5.85           (k1_tarski @ (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['84', '88'])).
% 5.68/5.85  thf('90', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_boole])).
% 5.68/5.85  thf('91', plain,
% 5.68/5.85      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X4 @ X2)
% 5.68/5.85          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['37'])).
% 5.68/5.85  thf('92', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['90', '91'])).
% 5.68/5.85  thf('93', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.68/5.85      inference('condensation', [status(thm)], ['92'])).
% 5.68/5.85  thf('94', plain,
% 5.68/5.85      ((r2_hidden @ sk_B @ 
% 5.68/5.85        (k1_tarski @ (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))),
% 5.68/5.85      inference('clc', [status(thm)], ['89', '93'])).
% 5.68/5.85  thf('95', plain,
% 5.68/5.85      (![X13 : $i, X16 : $i]:
% 5.68/5.85         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['26'])).
% 5.68/5.85  thf('96', plain,
% 5.68/5.85      (((sk_B) = (k1_funct_1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['94', '95'])).
% 5.68/5.85  thf('97', plain,
% 5.68/5.85      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 5.68/5.85         (~ (v1_funct_1 @ X57)
% 5.68/5.85          | ~ (v1_funct_2 @ X57 @ X58 @ X59)
% 5.68/5.85          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 5.68/5.85          | (r2_relset_1 @ X58 @ X59 @ X60 @ X57)
% 5.68/5.85          | ((k1_funct_1 @ X60 @ (sk_E @ X57 @ X60 @ X58))
% 5.68/5.85              != (k1_funct_1 @ X57 @ (sk_E @ X57 @ X60 @ X58)))
% 5.68/5.85          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 5.68/5.85          | ~ (v1_funct_2 @ X60 @ X58 @ X59)
% 5.68/5.85          | ~ (v1_funct_1 @ X60))),
% 5.68/5.85      inference('cnf', [status(esa)], [t18_funct_2])).
% 5.68/5.85  thf('98', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)) != (sk_B))
% 5.68/5.85          | ~ (v1_funct_1 @ sk_C_1)
% 5.68/5.85          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ X0)
% 5.68/5.85          | ~ (v1_funct_1 @ sk_D_1))),
% 5.68/5.85      inference('sup-', [status(thm)], ['96', '97'])).
% 5.68/5.85  thf('99', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 5.68/5.85      inference('simplify', [status(thm)], ['2'])).
% 5.68/5.85  thf('100', plain, ((r2_hidden @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A) @ sk_A)),
% 5.68/5.85      inference('clc', [status(thm)], ['14', '15'])).
% 5.68/5.85  thf('101', plain,
% 5.68/5.85      ((m1_subset_1 @ sk_C_1 @ 
% 5.68/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('102', plain,
% 5.68/5.85      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X61 @ X62)
% 5.68/5.85          | ((X63) = (k1_xboole_0))
% 5.68/5.85          | ~ (v1_funct_1 @ X64)
% 5.68/5.85          | ~ (v1_funct_2 @ X64 @ X62 @ X63)
% 5.68/5.85          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 5.68/5.85          | (r2_hidden @ (k1_funct_1 @ X64 @ X61) @ X63))),
% 5.68/5.85      inference('cnf', [status(esa)], [t7_funct_2])).
% 5.68/5.85  thf('103', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 5.68/5.85          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 5.68/5.85          | ~ (v1_funct_1 @ sk_C_1)
% 5.68/5.85          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ X0 @ sk_A))),
% 5.68/5.85      inference('sup-', [status(thm)], ['101', '102'])).
% 5.68/5.85  thf('104', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('106', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 5.68/5.85          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ X0 @ sk_A))),
% 5.68/5.85      inference('demod', [status(thm)], ['103', '104', '105'])).
% 5.68/5.85  thf('107', plain,
% 5.68/5.85      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85        | (r2_hidden @ 
% 5.68/5.85           (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)) @ 
% 5.68/5.85           (k1_tarski @ sk_B)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['100', '106'])).
% 5.68/5.85  thf('108', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 5.68/5.85          | (r2_hidden @ X0 @ X1)
% 5.68/5.85          | ~ (r2_hidden @ X2 @ X1))),
% 5.68/5.85      inference('sup-', [status(thm)], ['36', '38'])).
% 5.68/5.85  thf('109', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ 
% 5.68/5.85               (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)) @ X0)
% 5.68/5.85          | (r2_hidden @ sk_B @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['107', '108'])).
% 5.68/5.85  thf('110', plain,
% 5.68/5.85      (((r2_hidden @ sk_B @ 
% 5.68/5.85         (k1_tarski @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['99', '109'])).
% 5.68/5.85  thf('111', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 5.68/5.85          | ~ (r2_hidden @ X0 @ X1))),
% 5.68/5.85      inference('simplify', [status(thm)], ['74'])).
% 5.68/5.85  thf('112', plain,
% 5.68/5.85      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 5.68/5.85        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 5.68/5.85            (k1_tarski @ 
% 5.68/5.85             (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85            = (k1_xboole_0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['110', '111'])).
% 5.68/5.85  thf('113', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (((k1_tarski @ X0) != (k1_xboole_0))
% 5.68/5.85          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 5.68/5.85      inference('eq_fact', [status(thm)], ['82'])).
% 5.68/5.85  thf('114', plain,
% 5.68/5.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ 
% 5.68/5.85         (k1_tarski @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))
% 5.68/5.85         = (k1_xboole_0))),
% 5.68/5.85      inference('clc', [status(thm)], ['112', '113'])).
% 5.68/5.85  thf('115', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((r2_hidden @ X0 @ X1)
% 5.68/5.85          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['85', '87'])).
% 5.68/5.85  thf('116', plain,
% 5.68/5.85      (((r2_hidden @ sk_B @ k1_xboole_0)
% 5.68/5.85        | (r2_hidden @ sk_B @ 
% 5.68/5.85           (k1_tarski @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['114', '115'])).
% 5.68/5.85  thf('117', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.68/5.85      inference('condensation', [status(thm)], ['92'])).
% 5.68/5.85  thf('118', plain,
% 5.68/5.85      ((r2_hidden @ sk_B @ 
% 5.68/5.85        (k1_tarski @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A))))),
% 5.68/5.85      inference('clc', [status(thm)], ['116', '117'])).
% 5.68/5.85  thf('119', plain,
% 5.68/5.85      (![X13 : $i, X16 : $i]:
% 5.68/5.85         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 5.68/5.85      inference('simplify', [status(thm)], ['26'])).
% 5.68/5.85  thf('120', plain,
% 5.68/5.85      (((sk_B) = (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_A)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['118', '119'])).
% 5.68/5.85  thf('121', plain, ((v1_funct_1 @ sk_C_1)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('122', plain, ((v1_funct_1 @ sk_D_1)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('123', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         (((sk_B) != (sk_B))
% 5.68/5.85          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['98', '120', '121', '122'])).
% 5.68/5.85  thf('124', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         (~ (v1_funct_2 @ sk_D_1 @ sk_A @ X0)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D_1)
% 5.68/5.85          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.68/5.85          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0))),
% 5.68/5.85      inference('simplify', [status(thm)], ['123'])).
% 5.68/5.85  thf('125', plain,
% 5.68/5.85      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 5.68/5.85        | ~ (m1_subset_1 @ sk_C_1 @ 
% 5.68/5.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 5.68/5.85        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)
% 5.68/5.85        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['1', '124'])).
% 5.68/5.85  thf('126', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('127', plain,
% 5.68/5.85      ((m1_subset_1 @ sk_C_1 @ 
% 5.68/5.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('128', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('129', plain,
% 5.68/5.85      ((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D_1)),
% 5.68/5.85      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 5.68/5.85  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 5.68/5.85  
% 5.68/5.85  % SZS output end Refutation
% 5.68/5.85  
% 5.68/5.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
