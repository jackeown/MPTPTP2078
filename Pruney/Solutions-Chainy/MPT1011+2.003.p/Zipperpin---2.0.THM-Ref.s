%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v7X0PWDsMI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  798 (2846 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( r2_relset_1 @ X10 @ X11 @ X12 @ X9 )
      | ( r2_hidden @ ( sk_E @ X9 @ X12 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X13 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X13 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( r2_relset_1 @ X10 @ X11 @ X12 @ X9 )
      | ( ( k1_funct_1 @ X12 @ ( sk_E @ X9 @ X12 @ X10 ) )
       != ( k1_funct_1 @ X9 @ ( sk_E @ X9 @ X12 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','46'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('48',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v7X0PWDsMI
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 95 iterations in 0.095s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(t66_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56             ( m1_subset_1 @
% 0.21/0.56               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56           ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56            ( m1_subset_1 @
% 0.21/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56          ( ![D:$i]:
% 0.21/0.56            ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.56                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56                ( m1_subset_1 @
% 0.21/0.56                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56              ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t66_funct_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t18_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56           ( ( ![E:$i]:
% 0.21/0.56               ( ( r2_hidden @ E @ A ) =>
% 0.21/0.56                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.21/0.56             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X9)
% 0.21/0.56          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.56          | (r2_relset_1 @ X10 @ X11 @ X12 @ X9)
% 0.21/0.56          | (r2_hidden @ (sk_E @ X9 @ X12 @ X10) @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.56          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.21/0.56          | ~ (v1_funct_1 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.21/0.56          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.21/0.56          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D)
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.21/0.56          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.21/0.56          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.21/0.56        | (r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.56  thf('9', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.21/0.56        | (r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t7_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.56          | ((X15) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.56          | (r2_hidden @ (k1_funct_1 @ X16 @ X13) @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.21/0.56           (k1_tarski @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.56  thf(d1_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i]:
% 0.21/0.56         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.56  thf('24', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.56          | ((X15) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.56          | (r2_hidden @ (k1_funct_1 @ X16 @ X13) @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | (r2_hidden @ (k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.21/0.56           (k1_tarski @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i]:
% 0.21/0.56         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X9)
% 0.21/0.56          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.56          | (r2_relset_1 @ X10 @ X11 @ X12 @ X9)
% 0.21/0.56          | ((k1_funct_1 @ X12 @ (sk_E @ X9 @ X12 @ X10))
% 0.21/0.56              != (k1_funct_1 @ X9 @ (sk_E @ X9 @ X12 @ X10)))
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.56          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.21/0.56          | ~ (v1_funct_1 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_B) != (sk_B))
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.21/0.56          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.56        | ~ (m1_subset_1 @ sk_D @ 
% 0.21/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.21/0.56        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '40'])).
% 0.21/0.56  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('47', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.56      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.56  thf('48', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.56  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
