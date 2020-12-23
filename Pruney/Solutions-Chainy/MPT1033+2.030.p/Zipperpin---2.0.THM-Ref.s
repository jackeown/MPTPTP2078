%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCWHGevJzi

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 251 expanded)
%              Number of leaves         :   30 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  734 (4422 expanded)
%              Number of equality atoms :   34 ( 202 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X24 = X21 )
      | ~ ( r1_partfun1 @ X24 @ X21 )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_partfun1 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ( sk_C_2 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(rc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_partfun1])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X2 @ X1 ) )
      | ( X0
        = ( sk_C_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_C_2
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2
        = ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2
        = ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X2 @ X1 ) )
      | ( X0
        = ( sk_C_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_D
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( sk_D = sk_C_2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( sk_D = sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_D = sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','63'])).

thf('65',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['46','48'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCWHGevJzi
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 140 iterations in 0.070s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(t142_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52           ( ( r1_partfun1 @ C @ D ) =>
% 0.20/0.52             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.52               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52          ( ![D:$i]:
% 0.20/0.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52              ( ( r1_partfun1 @ C @ D ) =>
% 0.20/0.52                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.52                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.20/0.52  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc5_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.52          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.52          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.20/0.52          | ~ (v1_funct_1 @ X16)
% 0.20/0.52          | (v1_xboole_0 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.20/0.52        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t148_partfun1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.20/0.52               ( r1_partfun1 @ C @ D ) ) =>
% 0.20/0.52             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X21)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | ((X24) = (X21))
% 0.20/0.52          | ~ (r1_partfun1 @ X24 @ X21)
% 0.20/0.52          | ~ (v1_partfun1 @ X21 @ X22)
% 0.20/0.52          | ~ (v1_partfun1 @ X24 @ X22)
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | ~ (v1_funct_1 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.52          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.20/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.20/0.52          | ((X0) = (sk_D))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.52          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.20/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.20/0.52          | ((X0) = (sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ sk_B)
% 0.20/0.52          | ((X0) = (sk_D))
% 0.20/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.20/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.52          | ~ (v1_funct_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ sk_C_2)
% 0.20/0.52        | ~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 0.20/0.52        | ~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 0.20/0.52        | ((sk_C_2) = (sk_D))
% 0.20/0.52        | (v1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.52  thf('15', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, ((r1_partfun1 @ sk_C_2 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 0.20/0.52        | ((sk_C_2) = (sk_D))
% 0.20/0.52        | (v1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.52          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.52          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.20/0.52          | ~ (v1_funct_1 @ X16)
% 0.20/0.52          | (v1_xboole_0 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.20/0.52        | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.52  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('26', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.52  thf(fc3_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t5_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (v1_xboole_0 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i]: (((sk_C_2) = (sk_D)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.20/0.52  thf(rc1_partfun1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ?[C:$i]:
% 0.20/0.52       ( ( v1_funct_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.20/0.52         ( v4_relat_1 @ C @ A ) & ( v1_relat_1 @ C ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (m1_subset_1 @ (sk_C_1 @ X19 @ X20) @ 
% 0.20/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc1_partfun1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (v1_xboole_0 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.52          | ~ (r2_hidden @ X2 @ (sk_C_1 @ X0 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (sk_C_1 @ X0 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (sk_C_1 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X2 @ X1))
% 0.20/0.52          | ((X0) = (sk_C_1 @ X2 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((sk_C_2) = (sk_D))
% 0.20/0.52          | ((sk_C_2) = (sk_C_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.52  thf('44', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ((sk_C_2) = (sk_C_1 @ X0 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.52      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.52      inference('condensation', [status(thm)], ['47'])).
% 0.20/0.52  thf('49', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0) | ((sk_C_2) = (sk_C_1 @ X0 @ X1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('52', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (v1_xboole_0 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i]: (((sk_C_2) = (sk_D)) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X2 @ X1))
% 0.20/0.52          | ((X0) = (sk_C_1 @ X2 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((sk_C_2) = (sk_D))
% 0.20/0.52          | ((sk_D) = (sk_C_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X1 : $i]:
% 0.20/0.52         (((sk_D) = (sk_C_2))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | ((sk_C_2) = (sk_D)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['50', '61'])).
% 0.20/0.52  thf('63', plain, (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((sk_D) = (sk_C_2)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.52  thf('64', plain, ((((sk_C_2) = (sk_D)) | ((sk_D) = (sk_C_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '63'])).
% 0.20/0.52  thf('65', plain, (((sk_C_2) = (sk_D))),
% 0.20/0.52      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.52  thf('66', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '48'])).
% 0.20/0.52  thf('67', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '65', '66'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
