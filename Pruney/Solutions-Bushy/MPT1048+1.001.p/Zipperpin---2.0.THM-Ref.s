%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fxg8GvsUd2

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:58 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 294 expanded)
%              Number of leaves         :   26 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          : 1526 (5463 expanded)
%              Number of equality atoms :   13 (  54 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_relset_1_type,type,(
    r1_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t165_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_relset_1 @ A @ B @ D @ C )
           => ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_relset_1 @ A @ B @ D @ C )
             => ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t165_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X14 @ X15 @ X16 ) @ X19 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X14 @ X15 @ X16 ) @ X19 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_relat_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_partfun1 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t140_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_relat_1 @ E )
                & ( v1_funct_1 @ E ) )
             => ( ( ( r1_partfun1 @ C @ E )
                  & ( r1_relset_1 @ A @ B @ D @ C ) )
               => ( r1_partfun1 @ D @ E ) ) ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( r1_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ~ ( r1_partfun1 @ X25 @ X26 )
      | ( r1_partfun1 @ X22 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t140_partfun1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_1 @ X8 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_partfun1 @ X8 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_partfun1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X12 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X8 != X9 )
      | ~ ( v1_partfun1 @ X8 @ X12 )
      | ~ ( r1_partfun1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    ! [X7: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( r1_partfun1 @ X7 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X20 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).


%------------------------------------------------------------------------------
