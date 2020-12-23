%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sMd49fb9G

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:23 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 297 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          : 1555 (5492 expanded)
%              Number of equality atoms :   13 (  54 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_relset_1_type,type,(
    r1_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_relat_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_partfun1 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( r1_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ~ ( r1_partfun1 @ X26 @ X27 )
      | ( r1_partfun1 @ X23 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t140_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_partfun1 @ sk_D @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ X0 )
      | ( r1_partfun1 @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_partfun1 @ sk_D @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_partfun1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( X9 != X10 )
      | ~ ( v1_partfun1 @ X9 @ X13 )
      | ~ ( r1_partfun1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_partfun1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k5_partfun1 @ sk_A @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sMd49fb9G
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.85  % Solved by: fo/fo7.sh
% 0.59/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.85  % done 705 iterations in 0.398s
% 0.59/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.85  % SZS output start Refutation
% 0.59/0.85  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.59/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.59/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.85  thf(r1_relset_1_type, type, r1_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.85  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.59/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.85  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.59/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.85  thf(t165_funct_2, conjecture,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85       ( ![D:$i]:
% 0.59/0.85         ( ( ( v1_funct_1 @ D ) & 
% 0.59/0.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85           ( ( r1_relset_1 @ A @ B @ D @ C ) =>
% 0.59/0.85             ( r1_tarski @
% 0.59/0.85               ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) ))).
% 0.59/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.85        ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.85            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85          ( ![D:$i]:
% 0.59/0.85            ( ( ( v1_funct_1 @ D ) & 
% 0.59/0.85                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85              ( ( r1_relset_1 @ A @ B @ D @ C ) =>
% 0.59/0.85                ( r1_tarski @
% 0.59/0.85                  ( k5_partfun1 @ A @ B @ C ) @ ( k5_partfun1 @ A @ B @ D ) ) ) ) ) ) )),
% 0.59/0.85    inference('cnf.neg', [status(esa)], [t165_funct_2])).
% 0.59/0.85  thf('0', plain,
% 0.59/0.85      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.59/0.85          (k5_partfun1 @ sk_A @ sk_B @ sk_D))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(d3_tarski, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.85  thf('1', plain,
% 0.59/0.85      (![X1 : $i, X3 : $i]:
% 0.59/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.85  thf('2', plain,
% 0.59/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(d7_partfun1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.85         ( v1_funct_1 @ C ) ) =>
% 0.59/0.85       ( ![D:$i]:
% 0.59/0.85         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.59/0.85           ( ![E:$i]:
% 0.59/0.85             ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.85               ( ?[F:$i]:
% 0.59/0.85                 ( ( v1_funct_1 @ F ) & 
% 0.59/0.85                   ( m1_subset_1 @
% 0.59/0.85                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.85                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.59/0.85                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.59/0.85  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.59/0.85  thf(zf_stmt_2, axiom,
% 0.59/0.85    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.59/0.85     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.59/0.85       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.59/0.85         ( ( F ) = ( E ) ) & 
% 0.59/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.85         ( v1_funct_1 @ F ) ) ))).
% 0.59/0.85  thf(zf_stmt_3, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85       ( ![D:$i]:
% 0.59/0.85         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.59/0.85           ( ![E:$i]:
% 0.59/0.85             ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.85               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.59/0.85  thf('3', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.59/0.85         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 0.59/0.85          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 0.59/0.85             X16 @ X17)
% 0.59/0.85          | ~ (r2_hidden @ X20 @ X19)
% 0.59/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.59/0.85          | ~ (v1_funct_1 @ X15))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.85  thf('4', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ X15)
% 0.59/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.59/0.85          | ~ (r2_hidden @ X20 @ (k5_partfun1 @ X17 @ X16 @ X15))
% 0.59/0.85          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 0.59/0.85             X16 @ X17))),
% 0.59/0.85      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.85  thf('5', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A) @ X0 @ 
% 0.59/0.85           sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.59/0.85          | ~ (v1_funct_1 @ sk_C_1))),
% 0.59/0.85      inference('sup-', [status(thm)], ['2', '4'])).
% 0.59/0.85  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('7', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A) @ X0 @ 
% 0.59/0.85           sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.85      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.85  thf('8', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('9', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.85         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('10', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.85  thf('11', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('12', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.85         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.59/0.85          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('13', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (m1_subset_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.85  thf(cc2_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ![B:$i]:
% 0.59/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.85  thf('14', plain,
% 0.59/0.85      (![X4 : $i, X5 : $i]:
% 0.59/0.85         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.59/0.85          | (v1_relat_1 @ X4)
% 0.59/0.85          | ~ (v1_relat_1 @ X5))),
% 0.59/0.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.85  thf('15', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.59/0.85          | (v1_relat_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.85  thf(fc6_relat_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.85  thf('16', plain,
% 0.59/0.85      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.59/0.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.85  thf('17', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_relat_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.85      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.85  thf('18', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((v1_relat_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['10', '17'])).
% 0.59/0.85  thf('19', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_relat_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.85  thf('20', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.85  thf('21', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('22', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.85         ((r1_partfun1 @ X8 @ X9)
% 0.59/0.85          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('23', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_C_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.85  thf('24', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_partfun1 @ sk_C_1 @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['20', '23'])).
% 0.59/0.85  thf('25', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_C_1 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.85  thf('26', plain,
% 0.59/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('27', plain,
% 0.59/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t140_partfun1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85       ( ![D:$i]:
% 0.59/0.85         ( ( ( v1_funct_1 @ D ) & 
% 0.59/0.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.85           ( ![E:$i]:
% 0.59/0.85             ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.59/0.85               ( ( ( r1_partfun1 @ C @ E ) & ( r1_relset_1 @ A @ B @ D @ C ) ) =>
% 0.59/0.85                 ( r1_partfun1 @ D @ E ) ) ) ) ) ) ))).
% 0.59/0.85  thf('28', plain,
% 0.59/0.85      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ X23)
% 0.59/0.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.59/0.85          | ~ (r1_relset_1 @ X24 @ X25 @ X23 @ X26)
% 0.59/0.85          | ~ (r1_partfun1 @ X26 @ X27)
% 0.59/0.85          | (r1_partfun1 @ X23 @ X27)
% 0.59/0.85          | ~ (v1_funct_1 @ X27)
% 0.59/0.85          | ~ (v1_relat_1 @ X27)
% 0.59/0.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.59/0.85          | ~ (v1_funct_1 @ X26))),
% 0.59/0.85      inference('cnf', [status(esa)], [t140_partfun1])).
% 0.59/0.85  thf('29', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ X0)
% 0.59/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_funct_1 @ X1)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ X1)
% 0.59/0.85          | ~ (r1_partfun1 @ X0 @ X1)
% 0.59/0.85          | ~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.59/0.85          | ~ (v1_funct_1 @ sk_D))),
% 0.59/0.85      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.85  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('31', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ X0)
% 0.59/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_funct_1 @ X1)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ X1)
% 0.59/0.85          | ~ (r1_partfun1 @ X0 @ X1)
% 0.59/0.85          | ~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.85  thf('32', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         (~ (r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1)
% 0.59/0.85          | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ X0)
% 0.59/0.85          | ~ (v1_funct_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_funct_1 @ sk_C_1))),
% 0.59/0.85      inference('sup-', [status(thm)], ['26', '31'])).
% 0.59/0.85  thf('33', plain, ((r1_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('35', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         (~ (r1_partfun1 @ sk_C_1 @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ X0)
% 0.59/0.85          | ~ (v1_funct_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X0))),
% 0.59/0.85      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.59/0.85  thf('36', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_partfun1 @ sk_D @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['25', '35'])).
% 0.59/0.85  thf('37', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['19', '36'])).
% 0.59/0.85  thf('38', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_partfun1 @ sk_D @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('simplify', [status(thm)], ['37'])).
% 0.59/0.85  thf('39', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.85  thf('40', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('41', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.85         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('42', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_funct_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.85  thf('43', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['39', '42'])).
% 0.59/0.85  thf('44', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.85  thf('45', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_partfun1 @ sk_D @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('clc', [status(thm)], ['38', '44'])).
% 0.59/0.85  thf('46', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.85  thf('47', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.85  thf('48', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('49', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.85         ((v1_partfun1 @ X9 @ X12)
% 0.59/0.85          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('50', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_partfun1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.85  thf('51', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((v1_partfun1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85           sk_A)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['47', '50'])).
% 0.59/0.85  thf('52', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (v1_partfun1 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A))),
% 0.59/0.85      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.85  thf('53', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ((sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A)
% 0.59/0.85              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.85  thf('54', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (m1_subset_1 @ 
% 0.59/0.85             (sk_F_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85              sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.85  thf('55', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((m1_subset_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['53', '54'])).
% 0.59/0.85  thf('56', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (m1_subset_1 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['55'])).
% 0.59/0.85  thf('57', plain,
% 0.59/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13)
% 0.59/0.85          | ~ (v1_funct_1 @ X9)
% 0.59/0.85          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 0.59/0.85          | ((X9) != (X10))
% 0.59/0.85          | ~ (v1_partfun1 @ X9 @ X13)
% 0.59/0.85          | ~ (r1_partfun1 @ X8 @ X9))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.85  thf('58', plain,
% 0.59/0.85      (![X8 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.59/0.85         (~ (r1_partfun1 @ X8 @ X10)
% 0.59/0.85          | ~ (v1_partfun1 @ X10 @ X13)
% 0.59/0.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 0.59/0.85          | ~ (v1_funct_1 @ X10)
% 0.59/0.85          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13))),
% 0.59/0.85      inference('simplify', [status(thm)], ['57'])).
% 0.59/0.85  thf('59', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.59/0.85             sk_A)
% 0.59/0.85          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | ~ (v1_partfun1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A)
% 0.59/0.85          | ~ (r1_partfun1 @ X1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['56', '58'])).
% 0.59/0.85  thf('60', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ~ (r1_partfun1 @ X1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.59/0.85             sk_A)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['52', '59'])).
% 0.59/0.85  thf('61', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.59/0.85           sk_A)
% 0.59/0.85          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | ~ (r1_partfun1 @ X1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.85  thf('62', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | ~ (r1_partfun1 @ X1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.59/0.85             sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['46', '61'])).
% 0.59/0.85  thf('63', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B @ 
% 0.59/0.85           sk_A)
% 0.59/0.85          | ~ (r1_partfun1 @ X1 @ 
% 0.59/0.85               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('simplify', [status(thm)], ['62'])).
% 0.59/0.85  thf('64', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (zip_tseitin_0 @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_D @ 
% 0.59/0.85             sk_B @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['45', '63'])).
% 0.59/0.85  thf('65', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((zip_tseitin_0 @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_D @ sk_B @ 
% 0.59/0.85           sk_A)
% 0.59/0.85          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.59/0.85      inference('simplify', [status(thm)], ['64'])).
% 0.59/0.85  thf('66', plain,
% 0.59/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('67', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.59/0.85         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 0.59/0.85          | (r2_hidden @ X21 @ X19)
% 0.59/0.85          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 0.59/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.59/0.85          | ~ (v1_funct_1 @ X15))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.85  thf('68', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 0.59/0.85         (~ (v1_funct_1 @ X15)
% 0.59/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.59/0.85          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 0.59/0.85          | (r2_hidden @ X21 @ (k5_partfun1 @ X17 @ X16 @ X15)))),
% 0.59/0.85      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.85  thf('69', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.59/0.85          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A)
% 0.59/0.85          | ~ (v1_funct_1 @ sk_D))),
% 0.59/0.85      inference('sup-', [status(thm)], ['66', '68'])).
% 0.59/0.85  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('71', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.59/0.85          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A))),
% 0.59/0.85      inference('demod', [status(thm)], ['69', '70'])).
% 0.59/0.85  thf('72', plain,
% 0.59/0.85      (![X0 : $i]:
% 0.59/0.85         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.59/0.85          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.59/0.85             (k5_partfun1 @ sk_A @ sk_B @ sk_D)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['65', '71'])).
% 0.59/0.85  thf('73', plain,
% 0.59/0.85      (![X1 : $i, X3 : $i]:
% 0.59/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.85  thf('74', plain,
% 0.59/0.85      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.59/0.85         (k5_partfun1 @ sk_A @ sk_B @ sk_D))
% 0.59/0.85        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.59/0.85           (k5_partfun1 @ sk_A @ sk_B @ sk_D)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.85  thf('75', plain,
% 0.59/0.85      ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.59/0.85        (k5_partfun1 @ sk_A @ sk_B @ sk_D))),
% 0.59/0.85      inference('simplify', [status(thm)], ['74'])).
% 0.59/0.85  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.59/0.85  
% 0.59/0.85  % SZS output end Refutation
% 0.59/0.85  
% 0.72/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
