%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.le3qcwGPJn

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:08 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 567 expanded)
%              Number of leaves         :   26 ( 173 expanded)
%              Depth                    :   23
%              Number of atoms          :  717 (10854 expanded)
%              Number of equality atoms :   40 ( 515 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X26 = X23 )
      | ~ ( r1_partfun1 @ X26 @ X23 )
      | ~ ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_partfun1 @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = sk_D ) ),
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
    | ( sk_C_1 = sk_D ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( sk_C_1 = sk_D ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','49'])).

thf('51',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['0','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('53',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','49'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( k1_xboole_0 = sk_D ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( k1_xboole_0 = sk_D ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_D )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( k1_xboole_0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_D )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = sk_D ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( k1_xboole_0 = sk_D ) ),
    inference('sup-',[status(thm)],['54','66'])).

thf('68',plain,(
    k1_xboole_0 = sk_D ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['51','68','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.le3qcwGPJn
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 191 iterations in 0.101s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.55  thf(t142_funct_2, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55           ( ( r1_partfun1 @ C @ D ) =>
% 0.36/0.55             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.36/0.55               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55          ( ![D:$i]:
% 0.36/0.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55              ( ( r1_partfun1 @ C @ D ) =>
% 0.36/0.56                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.36/0.56                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.36/0.56  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc5_funct_2, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.56       ( ![C:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.36/0.56             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.36/0.56          | (v1_partfun1 @ X20 @ X21)
% 0.36/0.56          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.36/0.56          | ~ (v1_funct_1 @ X20)
% 0.36/0.56          | (v1_xboole_0 @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (((v1_xboole_0 @ sk_B)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.36/0.56        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.36/0.56        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t148_partfun1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.56       ( ![D:$i]:
% 0.36/0.56         ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.56           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.36/0.56               ( r1_partfun1 @ C @ D ) ) =>
% 0.36/0.56             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.56         (~ (v1_funct_1 @ X23)
% 0.36/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.56          | ((X26) = (X23))
% 0.36/0.56          | ~ (r1_partfun1 @ X26 @ X23)
% 0.36/0.56          | ~ (v1_partfun1 @ X23 @ X24)
% 0.36/0.56          | ~ (v1_partfun1 @ X26 @ X24)
% 0.36/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.56          | ~ (v1_funct_1 @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_funct_1 @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.56          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.56          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.36/0.56          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.36/0.56          | ((X0) = (sk_D))
% 0.36/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_funct_1 @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.56          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.56          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.36/0.56          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.36/0.56          | ((X0) = (sk_D)))),
% 0.36/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ sk_B)
% 0.36/0.56          | ((X0) = (sk_D))
% 0.36/0.56          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.36/0.56          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.56          | ~ (v1_funct_1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '12'])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      ((~ (v1_funct_1 @ sk_C_1)
% 0.36/0.56        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.36/0.56        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.36/0.56        | ((sk_C_1) = (sk_D))
% 0.36/0.56        | (v1_xboole_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '13'])).
% 0.36/0.56  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.36/0.56        | ((sk_C_1) = (sk_D))
% 0.36/0.56        | (v1_xboole_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.36/0.56          | (v1_partfun1 @ X20 @ X21)
% 0.36/0.56          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.36/0.56          | ~ (v1_funct_1 @ X20)
% 0.36/0.56          | (v1_xboole_0 @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (((v1_xboole_0 @ sk_B)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.56        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.56  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('26', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.56  thf(fc3_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t5_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.36/0.56          | ~ (v1_xboole_0 @ X15)
% 0.36/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X0 : $i]: (((sk_C_1) = (sk_D)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['26', '31'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['25', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf(t4_subset_1, axiom,
% 0.36/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.36/0.56          | ~ (v1_xboole_0 @ X15)
% 0.36/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.56  thf(d10_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (![X4 : $i, X6 : $i]:
% 0.36/0.56         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ X1)
% 0.36/0.56          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.36/0.56          | ((X0) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((sk_C_1) = (sk_D))
% 0.36/0.56          | ((sk_C_1) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['33', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      ((((sk_C_1) = (sk_D)) | ((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '41'])).
% 0.36/0.56  thf('43', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.56  thf('44', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)
% 0.36/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(reflexivity_r2_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.56       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.56         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.36/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.36/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.56      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.36/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.36/0.56  thf('49', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['46', '48'])).
% 0.36/0.56  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['45', '49'])).
% 0.36/0.56  thf('51', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 @ sk_D)),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '50'])).
% 0.36/0.56  thf('52', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_1) = (sk_D)))),
% 0.36/0.56      inference('clc', [status(thm)], ['17', '23'])).
% 0.36/0.56  thf('53', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['45', '49'])).
% 0.36/0.56  thf('54', plain, (((v1_xboole_0 @ sk_B) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('56', plain, (((v1_xboole_0 @ sk_B) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.36/0.56          | ~ (v1_xboole_0 @ X15)
% 0.36/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '60'])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (![X0 : $i]: (((k1_xboole_0) = (sk_D)) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['56', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['55', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ X1)
% 0.36/0.56          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.36/0.56          | ((X0) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_xboole_0) = (sk_D))
% 0.36/0.56          | ((sk_D) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['65'])).
% 0.36/0.56  thf('67', plain, ((((k1_xboole_0) = (sk_D)) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['54', '66'])).
% 0.36/0.56  thf('68', plain, (((k1_xboole_0) = (sk_D))),
% 0.36/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.36/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.56  thf('72', plain, ($false),
% 0.36/0.56      inference('demod', [status(thm)], ['51', '68', '71'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
