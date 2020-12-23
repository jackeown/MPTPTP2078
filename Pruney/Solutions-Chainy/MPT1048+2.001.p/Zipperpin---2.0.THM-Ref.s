%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.da6jlHwC6t

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:23 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 207 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          : 1522 (3630 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r1_relset_1_type,type,(
    r1_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t168_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k5_partfun1 @ X28 @ X29 @ X30 ) )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X14 @ X15 @ X16 ) @ X19 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X14 @ X15 @ X16 ) @ X19 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_partfun1 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
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

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k5_partfun1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_partfun1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t169_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
           => ( v1_partfun1 @ D @ A ) ) ) ) )).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_partfun1 @ X31 @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k5_partfun1 @ X32 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t169_partfun1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k5_partfun1 @ sk_A @ sk_B @ X1 ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X12 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X8 != X9 )
      | ~ ( v1_partfun1 @ X8 @ X12 )
      | ~ ( r1_partfun1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,(
    ! [X7: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( r1_partfun1 @ X7 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k5_partfun1 @ X16 @ X15 @ X14 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X20 @ ( k5_partfun1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.da6jlHwC6t
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.88/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.88/1.06  % Solved by: fo/fo7.sh
% 0.88/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.06  % done 457 iterations in 0.597s
% 0.88/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.88/1.06  % SZS output start Refutation
% 0.88/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.88/1.06  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.88/1.06  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.88/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.88/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.88/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.06  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.88/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.88/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.88/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.88/1.06  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.88/1.06  thf(r1_relset_1_type, type, r1_relset_1: $i > $i > $i > $i > $o).
% 0.88/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.88/1.06  thf(t165_funct_2, conjecture,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( ( v1_funct_1 @ D ) & 
% 0.88/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06           ( ( r1_relset_1 @ A @ B @ D @ C ) =>
% 0.88/1.06             ( r1_tarski @
% 0.88/1.06               ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) ))).
% 0.88/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.88/1.06        ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06          ( ![D:$i]:
% 0.88/1.06            ( ( ( v1_funct_1 @ D ) & 
% 0.88/1.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06              ( ( r1_relset_1 @ A @ B @ D @ C ) =>
% 0.88/1.06                ( r1_tarski @
% 0.88/1.06                  ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) ) )),
% 0.88/1.06    inference('cnf.neg', [status(esa)], [t165_funct_2])).
% 0.88/1.06  thf('0', plain,
% 0.88/1.06      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.06          (k5_partfun1 @ sk_A @ sk_B @ sk_D))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(d3_tarski, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ B ) <=>
% 0.88/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.88/1.06  thf('1', plain,
% 0.88/1.06      (![X1 : $i, X3 : $i]:
% 0.88/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.06  thf('2', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t168_partfun1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.88/1.06           ( ( v1_funct_1 @ D ) & 
% 0.88/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 0.88/1.06  thf('3', plain,
% 0.88/1.06      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.88/1.06         (~ (r2_hidden @ X27 @ (k5_partfun1 @ X28 @ X29 @ X30))
% 0.88/1.06          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.88/1.06          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.88/1.06          | ~ (v1_funct_1 @ X30))),
% 0.88/1.06      inference('cnf', [status(esa)], [t168_partfun1])).
% 0.88/1.06  thf('4', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ sk_C_1)
% 0.88/1.06          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.88/1.06  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('6', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('demod', [status(thm)], ['4', '5'])).
% 0.88/1.06  thf('7', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (m1_subset_1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['1', '6'])).
% 0.88/1.06  thf(cc1_relset_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.88/1.06       ( v1_relat_1 @ C ) ))).
% 0.88/1.06  thf('8', plain,
% 0.88/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.88/1.06         ((v1_relat_1 @ X4)
% 0.88/1.06          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.88/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.88/1.06  thf('9', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (v1_relat_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['7', '8'])).
% 0.88/1.06  thf('10', plain,
% 0.88/1.06      (![X1 : $i, X3 : $i]:
% 0.88/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.06  thf('11', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(d7_partfun1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.88/1.06         ( v1_funct_1 @ C ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.88/1.06           ( ![E:$i]:
% 0.88/1.06             ( ( r2_hidden @ E @ D ) <=>
% 0.88/1.06               ( ?[F:$i]:
% 0.88/1.06                 ( ( v1_funct_1 @ F ) & 
% 0.88/1.06                   ( m1_subset_1 @
% 0.88/1.06                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.88/1.06                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.88/1.06                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.88/1.06  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.88/1.06  thf(zf_stmt_2, axiom,
% 0.88/1.06    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.88/1.06     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.88/1.06       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.88/1.06         ( ( F ) = ( E ) ) & 
% 0.88/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.88/1.06         ( v1_funct_1 @ F ) ) ))).
% 0.88/1.06  thf(zf_stmt_3, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.88/1.06           ( ![E:$i]:
% 0.88/1.06             ( ( r2_hidden @ E @ D ) <=>
% 0.88/1.06               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.88/1.06  thf('12', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.88/1.06         (((X18) != (k5_partfun1 @ X16 @ X15 @ X14))
% 0.88/1.06          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X14 @ X15 @ X16) @ X19 @ X14 @ 
% 0.88/1.06             X15 @ X16)
% 0.88/1.06          | ~ (r2_hidden @ X19 @ X18)
% 0.88/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.88/1.06          | ~ (v1_funct_1 @ X14))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.88/1.06  thf('13', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i, X16 : $i, X19 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X14)
% 0.88/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.88/1.06          | ~ (r2_hidden @ X19 @ (k5_partfun1 @ X16 @ X15 @ X14))
% 0.88/1.06          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X14 @ X15 @ X16) @ X19 @ X14 @ 
% 0.88/1.06             X15 @ X16))),
% 0.88/1.06      inference('simplify', [status(thm)], ['12'])).
% 0.88/1.06  thf('14', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A) @ X0 @ 
% 0.88/1.06           sk_C_1 @ sk_B @ sk_A)
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.88/1.06          | ~ (v1_funct_1 @ sk_C_1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['11', '13'])).
% 0.88/1.06  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('16', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A) @ X0 @ 
% 0.88/1.06           sk_C_1 @ sk_B @ sk_A)
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.88/1.06  thf('17', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06              sk_C_1 @ sk_B @ sk_A) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.88/1.06             sk_B @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['10', '16'])).
% 0.88/1.06  thf('18', plain,
% 0.88/1.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.88/1.06         (((X8) = (X9)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.06  thf('19', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06              sk_C_1 @ sk_B @ sk_A)
% 0.88/1.06              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.88/1.06  thf('20', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06              sk_C_1 @ sk_B @ sk_A) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.88/1.06             sk_B @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['10', '16'])).
% 0.88/1.06  thf('21', plain,
% 0.88/1.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.88/1.06         ((r1_partfun1 @ X7 @ X8)
% 0.88/1.06          | ~ (zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X11))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.06  thf('22', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_C_1 @ 
% 0.88/1.06             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06              sk_C_1 @ sk_B @ sk_A)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.88/1.06  thf('23', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_partfun1 @ sk_C_1 @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('sup+', [status(thm)], ['19', '22'])).
% 0.88/1.06  thf('24', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_C_1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('simplify', [status(thm)], ['23'])).
% 0.88/1.06  thf('25', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('26', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t140_partfun1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( ( v1_funct_1 @ D ) & 
% 0.88/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06           ( ![E:$i]:
% 0.88/1.06             ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.88/1.06               ( ( ( r1_partfun1 @ C @ E ) & ( r1_relset_1 @ A @ B @ D @ C ) ) =>
% 0.88/1.06                 ( r1_partfun1 @ D @ E ) ) ) ) ) ) ))).
% 0.88/1.06  thf('27', plain,
% 0.88/1.06      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X22)
% 0.88/1.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.88/1.06          | ~ (r1_relset_1 @ X23 @ X24 @ X22 @ X25)
% 0.88/1.06          | ~ (r1_partfun1 @ X25 @ X26)
% 0.88/1.06          | (r1_partfun1 @ X22 @ X26)
% 0.88/1.06          | ~ (v1_funct_1 @ X26)
% 0.88/1.06          | ~ (v1_relat_1 @ X26)
% 0.88/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.88/1.06          | ~ (v1_funct_1 @ X25))),
% 0.88/1.06      inference('cnf', [status(esa)], [t140_partfun1])).
% 0.88/1.06  thf('28', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (v1_relat_1 @ X1)
% 0.88/1.06          | ~ (v1_funct_1 @ X1)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ X1)
% 0.88/1.06          | ~ (r1_partfun1 @ X0 @ X1)
% 0.88/1.06          | ~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ sk_D))),
% 0.88/1.06      inference('sup-', [status(thm)], ['26', '27'])).
% 0.88/1.06  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('30', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (v1_relat_1 @ X1)
% 0.88/1.06          | ~ (v1_funct_1 @ X1)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ X1)
% 0.88/1.06          | ~ (r1_partfun1 @ X0 @ X1)
% 0.88/1.06          | ~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.88/1.06      inference('demod', [status(thm)], ['28', '29'])).
% 0.88/1.06  thf('31', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1)
% 0.88/1.06          | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ X0)
% 0.88/1.06          | ~ (v1_relat_1 @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ sk_C_1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['25', '30'])).
% 0.88/1.06  thf('32', plain, ((r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('34', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (r1_partfun1 @ sk_C_1 @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ X0)
% 0.88/1.06          | ~ (v1_relat_1 @ X0))),
% 0.88/1.06      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.88/1.06  thf('35', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (v1_relat_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_partfun1 @ sk_D @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['24', '34'])).
% 0.88/1.06  thf('36', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['9', '35'])).
% 0.88/1.06  thf('37', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_partfun1 @ sk_D @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['36'])).
% 0.88/1.06  thf('38', plain,
% 0.88/1.06      (![X1 : $i, X3 : $i]:
% 0.88/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.06  thf('39', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('40', plain,
% 0.88/1.06      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.88/1.06         (~ (r2_hidden @ X27 @ (k5_partfun1 @ X28 @ X29 @ X30))
% 0.88/1.06          | (v1_funct_1 @ X27)
% 0.88/1.06          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.88/1.06          | ~ (v1_funct_1 @ X30))),
% 0.88/1.06      inference('cnf', [status(esa)], [t168_partfun1])).
% 0.88/1.06  thf('41', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ sk_C_1)
% 0.88/1.06          | (v1_funct_1 @ X0)
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.88/1.06  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('43', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((v1_funct_1 @ X0)
% 0.88/1.06          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('demod', [status(thm)], ['41', '42'])).
% 0.88/1.06  thf('44', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['38', '43'])).
% 0.88/1.06  thf('45', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_partfun1 @ sk_D @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('clc', [status(thm)], ['37', '44'])).
% 0.88/1.06  thf('46', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['38', '43'])).
% 0.88/1.06  thf('47', plain,
% 0.88/1.06      (![X1 : $i, X3 : $i]:
% 0.88/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.06  thf('48', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (m1_subset_1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['1', '6'])).
% 0.88/1.06  thf(t169_partfun1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06       ( ![D:$i]:
% 0.88/1.06         ( ( ( v1_funct_1 @ D ) & 
% 0.88/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.06           ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.88/1.06             ( v1_partfun1 @ D @ A ) ) ) ) ))).
% 0.88/1.06  thf('49', plain,
% 0.88/1.06      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X31)
% 0.88/1.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.88/1.06          | (v1_partfun1 @ X31 @ X32)
% 0.88/1.06          | ~ (r2_hidden @ X31 @ (k5_partfun1 @ X32 @ X33 @ X34))
% 0.88/1.06          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.88/1.06          | ~ (v1_funct_1 @ X34))),
% 0.88/1.06      inference('cnf', [status(esa)], [t169_partfun1])).
% 0.88/1.06  thf('50', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ X1)
% 0.88/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (r2_hidden @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06               (k5_partfun1 @ sk_A @ sk_B @ X1))
% 0.88/1.06          | (v1_partfun1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['48', '49'])).
% 0.88/1.06  thf('51', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (v1_partfun1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A)
% 0.88/1.06          | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.88/1.06               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.06          | ~ (v1_funct_1 @ sk_C_1)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['47', '50'])).
% 0.88/1.06  thf('52', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('54', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (v1_partfun1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.88/1.06  thf('55', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((v1_partfun1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06           sk_A)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['54'])).
% 0.88/1.06  thf('56', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['38', '43'])).
% 0.88/1.06  thf('57', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (v1_partfun1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A))),
% 0.88/1.06      inference('clc', [status(thm)], ['55', '56'])).
% 0.88/1.06  thf('58', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (m1_subset_1 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['1', '6'])).
% 0.88/1.06  thf('59', plain,
% 0.88/1.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ X8 @ X9 @ X7 @ X10 @ X12)
% 0.88/1.06          | ~ (v1_funct_1 @ X8)
% 0.88/1.06          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.88/1.06          | ((X8) != (X9))
% 0.88/1.06          | ~ (v1_partfun1 @ X8 @ X12)
% 0.88/1.06          | ~ (r1_partfun1 @ X7 @ X8))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.06  thf('60', plain,
% 0.88/1.06      (![X7 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.88/1.06         (~ (r1_partfun1 @ X7 @ X9)
% 0.88/1.06          | ~ (v1_partfun1 @ X9 @ X12)
% 0.88/1.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.88/1.06          | ~ (v1_funct_1 @ X9)
% 0.88/1.06          | (zip_tseitin_0 @ X9 @ X9 @ X7 @ X10 @ X12))),
% 0.88/1.06      inference('simplify', [status(thm)], ['59'])).
% 0.88/1.06  thf('61', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.88/1.06             sk_A)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | ~ (v1_partfun1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A)
% 0.88/1.06          | ~ (r1_partfun1 @ X1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['58', '60'])).
% 0.88/1.06  thf('62', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (r1_partfun1 @ X1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.88/1.06             sk_A)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['57', '61'])).
% 0.88/1.06  thf('63', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.88/1.06           sk_A)
% 0.88/1.06          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | ~ (r1_partfun1 @ X1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['62'])).
% 0.88/1.06  thf('64', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | ~ (r1_partfun1 @ X1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.88/1.06             sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['46', '63'])).
% 0.88/1.06  thf('65', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.88/1.06           sk_A)
% 0.88/1.06          | ~ (r1_partfun1 @ X1 @ 
% 0.88/1.06               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['64'])).
% 0.88/1.06  thf('66', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (zip_tseitin_0 @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_D @ 
% 0.88/1.06             sk_B @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['45', '65'])).
% 0.88/1.06  thf('67', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((zip_tseitin_0 @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_D @ sk_B @ 
% 0.88/1.06           sk_A)
% 0.88/1.06          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['66'])).
% 0.88/1.06  thf('68', plain,
% 0.88/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('69', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.88/1.06         (((X18) != (k5_partfun1 @ X16 @ X15 @ X14))
% 0.88/1.06          | (r2_hidden @ X20 @ X18)
% 0.88/1.06          | ~ (zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16)
% 0.88/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.88/1.06          | ~ (v1_funct_1 @ X14))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.88/1.06  thf('70', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i, X16 : $i, X20 : $i, X21 : $i]:
% 0.88/1.06         (~ (v1_funct_1 @ X14)
% 0.88/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.88/1.06          | ~ (zip_tseitin_0 @ X21 @ X20 @ X14 @ X15 @ X16)
% 0.88/1.06          | (r2_hidden @ X20 @ (k5_partfun1 @ X16 @ X15 @ X14)))),
% 0.88/1.06      inference('simplify', [status(thm)], ['69'])).
% 0.88/1.06  thf('71', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.88/1.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A)
% 0.88/1.06          | ~ (v1_funct_1 @ sk_D))),
% 0.88/1.06      inference('sup-', [status(thm)], ['68', '70'])).
% 0.88/1.06  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('73', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.88/1.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A))),
% 0.88/1.06      inference('demod', [status(thm)], ['71', '72'])).
% 0.88/1.06  thf('74', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.06          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.06             (k5_partfun1 @ sk_A @ sk_B @ sk_D)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['67', '73'])).
% 0.88/1.06  thf('75', plain,
% 0.88/1.06      (![X1 : $i, X3 : $i]:
% 0.88/1.06         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.88/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.06  thf('76', plain,
% 0.88/1.06      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.06         (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.88/1.06        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.06           (k5_partfun1 @ sk_A @ sk_B @ sk_D)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['74', '75'])).
% 0.88/1.06  thf('77', plain,
% 0.88/1.06      ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.06        (k5_partfun1 @ sk_A @ sk_B @ sk_D))),
% 0.88/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.88/1.06  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.88/1.06  
% 0.88/1.06  % SZS output end Refutation
% 0.88/1.06  
% 0.88/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
