%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5cA1KjBZJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:32 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 119 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  691 (1829 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24 ) )
      | ( v2_funct_1 @ X28 )
      | ( X26 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X25 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','36','38'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('49',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5cA1KjBZJ
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 272 iterations in 0.128s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.57  thf(t37_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57            ( ?[D:$i]:
% 0.39/0.57              ( ( r2_relset_1 @
% 0.39/0.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.39/0.57                  ( k6_partfun1 @ A ) ) & 
% 0.39/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.39/0.57                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.39/0.57            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57               ( ?[D:$i]:
% 0.39/0.57                 ( ( r2_relset_1 @
% 0.39/0.57                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.39/0.57                     ( k6_partfun1 @ A ) ) & 
% 0.39/0.57                   ( m1_subset_1 @
% 0.39/0.57                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.39/0.57                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.39/0.57               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.39/0.57  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t3_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('3', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.39/0.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.39/0.57        (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k1_partfun1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( v1_funct_1 @ F ) & 
% 0.39/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.39/0.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.39/0.57          | ~ (v1_funct_1 @ X17)
% 0.39/0.57          | ~ (v1_funct_1 @ X20)
% 0.39/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.39/0.57          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_D)
% 0.39/0.57        | (m1_subset_1 @ 
% 0.39/0.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '10'])).
% 0.39/0.57  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      ((m1_subset_1 @ 
% 0.39/0.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.39/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.39/0.57          | ((X12) = (X15))
% 0.39/0.57          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.39/0.57             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.39/0.57          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.39/0.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.57            = (k6_partfun1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '15'])).
% 0.39/0.57  thf(t29_relset_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( m1_subset_1 @
% 0.39/0.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X16 : $i]:
% 0.39/0.57         (m1_subset_1 @ (k6_relat_1 @ X16) @ 
% 0.39/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.39/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.39/0.57  thf('18', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X16 : $i]:
% 0.39/0.57         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 0.39/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.57         = (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t26_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ![E:$i]:
% 0.39/0.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.39/0.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.57           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.39/0.57             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.57               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X24)
% 0.39/0.57          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.39/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.39/0.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24))
% 0.39/0.57          | (v2_funct_1 @ X28)
% 0.39/0.57          | ((X26) = (k1_xboole_0))
% 0.39/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.39/0.57          | ~ (v1_funct_2 @ X28 @ X27 @ X25)
% 0.39/0.57          | ~ (v1_funct_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.57          | ((sk_A) = (k1_xboole_0))
% 0.39/0.57          | (v2_funct_1 @ X0)
% 0.39/0.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.57          | ((sk_A) = (k1_xboole_0))
% 0.39/0.57          | (v2_funct_1 @ X0)
% 0.39/0.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.39/0.57        | (v2_funct_1 @ sk_C)
% 0.39/0.57        | ((sk_A) = (k1_xboole_0))
% 0.39/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.39/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '26'])).
% 0.39/0.57  thf(fc4_funct_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('28', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.39/0.57  thf('29', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.57  thf('30', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 0.39/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('34', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '30', '31', '32', '33'])).
% 0.39/0.57  thf('35', plain, (~ (v2_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.57      inference('clc', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf(t113_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.57  thf('39', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.39/0.57      inference('demod', [status(thm)], ['3', '36', '38'])).
% 0.39/0.57  thf(t3_xboole_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.57  thf('41', plain, (((sk_C) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X16 : $i]:
% 0.39/0.57         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 0.39/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('47', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.57  thf('49', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 0.39/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('51', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.39/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf('52', plain, ($false),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '41', '51'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
