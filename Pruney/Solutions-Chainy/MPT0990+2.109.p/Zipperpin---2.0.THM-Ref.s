%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.riFyOWpQyF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:13 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  382 (1609 expanded)
%              Number of leaves         :   54 ( 514 expanded)
%              Depth                    :   50
%              Number of atoms          : 3165 (28441 expanded)
%              Number of equality atoms :  190 (1900 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_partfun1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k6_partfun1 @ X0 ) )
        = ( k7_relat_1 @ sk_D @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('24',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('25',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference('sup-',[status(thm)],['1','28'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('30',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('31',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('36',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf('41',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference('sup-',[status(thm)],['1','28'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('44',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['56','61','62'])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('68',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('85',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('86',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( X39 = X42 )
      | ~ ( r2_relset_1 @ X40 @ X41 @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('89',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('90',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('92',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('93',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('98',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['92','95','96','97'])).

thf('99',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('106',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('112',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['99','112'])).

thf('114',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['44','113'])).

thf('115',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('116',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('118',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('119',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('120',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('121',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('122',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('123',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('124',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('127',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('130',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['125','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('147',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['124','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('150',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('155',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('156',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('158',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X31 ) @ X31 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('159',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('160',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X31 ) @ X31 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('161',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
       != ( k1_relat_1 @ X29 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('164',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('165',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['173','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['154','187'])).

thf('189',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('190',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('193',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('194',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('195',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('197',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('198',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_partfun1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['196','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('202',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('204',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['200','201'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('207',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('208',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['195','213'])).

thf('215',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('216',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','219','220','221','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['192','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v2_funct_1 @ X29 )
      | ( ( k2_relat_1 @ X28 )
       != ( k1_relat_1 @ X29 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('229',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('231',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('234',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233'])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['190','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','242'])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','244','245','246','247'])).

thf('249',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','249'])).

thf('251',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['123','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['122','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('257',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('260',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['121','260'])).

thf('262',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('263',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('265',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['261','262','263','264','265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('269',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['120','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('272',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('273',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['270','271','272','273','274'])).

thf('276',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','275'])).

thf('277',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['200','201'])).

thf('278',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('279',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['276','277','278','279','280'])).

thf('282',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('283',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['281','282'])).

thf('284',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('285',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['248'])).

thf('286',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','286'])).

thf('288',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('289',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','290'])).

thf('292',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('293',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('296',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['294','295'])).

thf('297',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','298'])).

thf('300',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('301',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['115','302'])).

thf('304',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('305',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['100','101'])).

thf('306',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('307',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('309',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('311',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_partfun1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['309','312'])).

thf('314',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('317',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['313','314','315','316'])).

thf('318',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['304','317'])).

thf('319',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('320',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['318','319','320'])).

thf('322',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('323',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['303','321','322'])).

thf('324',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','323'])).

thf('325',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['324','325'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.riFyOWpQyF
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:51 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.15/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.38  % Solved by: fo/fo7.sh
% 1.15/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.38  % done 1168 iterations in 0.913s
% 1.15/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.38  % SZS output start Refutation
% 1.15/1.38  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.15/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.38  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.15/1.38  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.38  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.38  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.15/1.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.38  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.15/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.38  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.15/1.38  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.15/1.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.38  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.38  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.15/1.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.38  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.15/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.38  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.15/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.38  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.38  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.38  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.15/1.38  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.15/1.38  thf(d10_xboole_0, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.38  thf('0', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.15/1.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.38  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.38      inference('simplify', [status(thm)], ['0'])).
% 1.15/1.38  thf(t36_funct_2, conjecture,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.38       ( ![D:$i]:
% 1.15/1.38         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.15/1.38             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.15/1.38           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.15/1.38               ( r2_relset_1 @
% 1.15/1.38                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.15/1.38                 ( k6_partfun1 @ A ) ) & 
% 1.15/1.38               ( v2_funct_1 @ C ) ) =>
% 1.15/1.38             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.15/1.38               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.15/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.38    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.38        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.38            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.38          ( ![D:$i]:
% 1.15/1.38            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.15/1.38                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.15/1.38              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.15/1.38                  ( r2_relset_1 @
% 1.15/1.38                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.15/1.38                    ( k6_partfun1 @ A ) ) & 
% 1.15/1.38                  ( v2_funct_1 @ C ) ) =>
% 1.15/1.38                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.15/1.38                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.15/1.38    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.15/1.38  thf('2', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(cc2_relset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.38  thf('3', plain,
% 1.15/1.38      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X33 @ X34)
% 1.15/1.38          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.15/1.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.38  thf('4', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.15/1.38      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.38  thf(t209_relat_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.15/1.38       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.15/1.38  thf('5', plain,
% 1.15/1.38      (![X13 : $i, X14 : $i]:
% 1.15/1.38         (((X13) = (k7_relat_1 @ X13 @ X14))
% 1.15/1.38          | ~ (v4_relat_1 @ X13 @ X14)
% 1.15/1.38          | ~ (v1_relat_1 @ X13))),
% 1.15/1.38      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.15/1.38  thf('6', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['4', '5'])).
% 1.15/1.38  thf('7', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(cc2_relat_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ A ) =>
% 1.15/1.38       ( ![B:$i]:
% 1.15/1.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.15/1.38  thf('8', plain,
% 1.15/1.38      (![X3 : $i, X4 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.38          | (v1_relat_1 @ X3)
% 1.15/1.38          | ~ (v1_relat_1 @ X4))),
% 1.15/1.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.38  thf('9', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup-', [status(thm)], ['7', '8'])).
% 1.15/1.38  thf(fc6_relat_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.15/1.38  thf('10', plain,
% 1.15/1.38      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.38  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('12', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['6', '11'])).
% 1.15/1.38  thf(t148_relat_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ B ) =>
% 1.15/1.38       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.15/1.38  thf('13', plain,
% 1.15/1.38      (![X9 : $i, X10 : $i]:
% 1.15/1.38         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 1.15/1.38          | ~ (v1_relat_1 @ X9))),
% 1.15/1.38      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.15/1.38  thf('14', plain,
% 1.15/1.38      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup+', [status(thm)], ['12', '13'])).
% 1.15/1.38  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('16', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.38  thf('17', plain,
% 1.15/1.38      (![X9 : $i, X10 : $i]:
% 1.15/1.38         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 1.15/1.38          | ~ (v1_relat_1 @ X9))),
% 1.15/1.38      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.15/1.38  thf(t79_relat_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ B ) =>
% 1.15/1.38       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.15/1.38         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.15/1.38  thf('18', plain,
% 1.15/1.38      (![X21 : $i, X22 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.15/1.38          | ((k5_relat_1 @ X21 @ (k6_relat_1 @ X22)) = (X21))
% 1.15/1.38          | ~ (v1_relat_1 @ X21))),
% 1.15/1.38      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.15/1.38  thf(redefinition_k6_partfun1, axiom,
% 1.15/1.38    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.15/1.38  thf('19', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('20', plain,
% 1.15/1.38      (![X21 : $i, X22 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.15/1.38          | ((k5_relat_1 @ X21 @ (k6_partfun1 @ X22)) = (X21))
% 1.15/1.38          | ~ (v1_relat_1 @ X21))),
% 1.15/1.38      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.38  thf('21', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 1.15/1.38          | ~ (v1_relat_1 @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.15/1.38          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_partfun1 @ X2))
% 1.15/1.38              = (k7_relat_1 @ X1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['17', '20'])).
% 1.15/1.38  thf('22', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.15/1.38          | ((k5_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ (k6_partfun1 @ X0))
% 1.15/1.38              = (k7_relat_1 @ sk_D @ sk_B))
% 1.15/1.38          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))
% 1.15/1.38          | ~ (v1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup-', [status(thm)], ['16', '21'])).
% 1.15/1.38  thf('23', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['6', '11'])).
% 1.15/1.38  thf('24', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['6', '11'])).
% 1.15/1.38  thf('25', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['6', '11'])).
% 1.15/1.38  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('28', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.15/1.38          | ((k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)) = (sk_D)))),
% 1.15/1.38      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 1.15/1.38  thf('29', plain,
% 1.15/1.38      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 1.15/1.38      inference('sup-', [status(thm)], ['1', '28'])).
% 1.15/1.38  thf(t78_relat_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ A ) =>
% 1.15/1.38       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.15/1.38  thf('30', plain,
% 1.15/1.38      (![X20 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X20)) @ X20) = (X20))
% 1.15/1.38          | ~ (v1_relat_1 @ X20))),
% 1.15/1.38      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.15/1.38  thf('31', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('32', plain,
% 1.15/1.38      (![X20 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X20)) @ X20) = (X20))
% 1.15/1.38          | ~ (v1_relat_1 @ X20))),
% 1.15/1.38      inference('demod', [status(thm)], ['30', '31'])).
% 1.15/1.38  thf(t55_relat_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ A ) =>
% 1.15/1.38       ( ![B:$i]:
% 1.15/1.38         ( ( v1_relat_1 @ B ) =>
% 1.15/1.38           ( ![C:$i]:
% 1.15/1.38             ( ( v1_relat_1 @ C ) =>
% 1.15/1.38               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.15/1.38                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.15/1.38  thf('33', plain,
% 1.15/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X15)
% 1.15/1.38          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 1.15/1.38              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 1.15/1.38          | ~ (v1_relat_1 @ X17)
% 1.15/1.38          | ~ (v1_relat_1 @ X16))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.38  thf('34', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (((k5_relat_1 @ X0 @ X1)
% 1.15/1.38            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.15/1.38               (k5_relat_1 @ X0 @ X1)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['32', '33'])).
% 1.15/1.38  thf(fc4_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.15/1.38       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.15/1.38  thf('35', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.15/1.38  thf('36', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('37', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 1.15/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.15/1.38  thf('38', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (((k5_relat_1 @ X0 @ X1)
% 1.15/1.38            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.15/1.38               (k5_relat_1 @ X0 @ X1)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['34', '37'])).
% 1.15/1.38  thf('39', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ X0 @ X1)
% 1.15/1.38              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.15/1.38                 (k5_relat_1 @ X0 @ X1))))),
% 1.15/1.38      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.38  thf('40', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.15/1.38          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_D)
% 1.15/1.38        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.15/1.38      inference('sup+', [status(thm)], ['29', '39'])).
% 1.15/1.38  thf('41', plain,
% 1.15/1.38      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 1.15/1.38      inference('sup-', [status(thm)], ['1', '28'])).
% 1.15/1.38  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('43', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 1.15/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.15/1.38  thf('44', plain,
% 1.15/1.38      (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 1.15/1.38      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 1.15/1.38  thf('45', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.15/1.38      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.38  thf(d18_relat_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ B ) =>
% 1.15/1.38       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.38  thf('46', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.38          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.38          | ~ (v1_relat_1 @ X5))),
% 1.15/1.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.38  thf('47', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['45', '46'])).
% 1.15/1.38  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.15/1.38      inference('demod', [status(thm)], ['47', '48'])).
% 1.15/1.38  thf('50', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(redefinition_k2_relset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.38       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.15/1.38  thf('51', plain,
% 1.15/1.38      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.15/1.38         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 1.15/1.38          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.15/1.38  thf('52', plain,
% 1.15/1.38      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['50', '51'])).
% 1.15/1.38  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('54', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf(t147_funct_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.15/1.38       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.15/1.38         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.15/1.38  thf('55', plain,
% 1.15/1.38      (![X26 : $i, X27 : $i]:
% 1.15/1.38         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 1.15/1.38          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 1.15/1.38          | ~ (v1_funct_1 @ X27)
% 1.15/1.38          | ~ (v1_relat_1 @ X27))),
% 1.15/1.38      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.15/1.38  thf('56', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (r1_tarski @ X0 @ sk_B)
% 1.15/1.38          | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38          | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['54', '55'])).
% 1.15/1.38  thf('57', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('58', plain,
% 1.15/1.38      (![X3 : $i, X4 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.38          | (v1_relat_1 @ X3)
% 1.15/1.38          | ~ (v1_relat_1 @ X4))),
% 1.15/1.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.38  thf('59', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['57', '58'])).
% 1.15/1.38  thf('60', plain,
% 1.15/1.38      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.38  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('63', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (r1_tarski @ X0 @ sk_B)
% 1.15/1.38          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['56', '61', '62'])).
% 1.15/1.38  thf('64', plain,
% 1.15/1.38      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.15/1.38         = (k1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup-', [status(thm)], ['49', '63'])).
% 1.15/1.38  thf('65', plain,
% 1.15/1.38      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.38        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.15/1.38        (k6_partfun1 @ sk_A))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('66', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('67', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(redefinition_k1_partfun1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.38     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.38         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.38         ( v1_funct_1 @ F ) & 
% 1.15/1.38         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.38       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.15/1.38  thf('68', plain,
% 1.15/1.38      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.15/1.38          | ~ (v1_funct_1 @ X51)
% 1.15/1.38          | ~ (v1_funct_1 @ X54)
% 1.15/1.38          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 1.15/1.38          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 1.15/1.38              = (k5_relat_1 @ X51 @ X54)))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.38  thf('69', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.15/1.38            = (k5_relat_1 @ sk_C @ X0))
% 1.15/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['67', '68'])).
% 1.15/1.38  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('71', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.15/1.38            = (k5_relat_1 @ sk_C @ X0))
% 1.15/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.38          | ~ (v1_funct_1 @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['69', '70'])).
% 1.15/1.38  thf('72', plain,
% 1.15/1.38      ((~ (v1_funct_1 @ sk_D)
% 1.15/1.38        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.38            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['66', '71'])).
% 1.15/1.38  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('74', plain,
% 1.15/1.38      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.38         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.15/1.38      inference('demod', [status(thm)], ['72', '73'])).
% 1.15/1.38  thf('75', plain,
% 1.15/1.38      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.15/1.38        (k6_partfun1 @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['65', '74'])).
% 1.15/1.38  thf('76', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('77', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(dt_k1_partfun1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.38     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.38         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.38         ( v1_funct_1 @ F ) & 
% 1.15/1.38         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.38       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.15/1.38         ( m1_subset_1 @
% 1.15/1.38           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.15/1.38           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.15/1.38  thf('78', plain,
% 1.15/1.38      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.15/1.38          | ~ (v1_funct_1 @ X43)
% 1.15/1.38          | ~ (v1_funct_1 @ X46)
% 1.15/1.38          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.15/1.38          | (m1_subset_1 @ (k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46) @ 
% 1.15/1.38             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X48))))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.15/1.38  thf('79', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.15/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.15/1.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.15/1.38          | ~ (v1_funct_1 @ X1)
% 1.15/1.38          | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['77', '78'])).
% 1.15/1.38  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('81', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.15/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.15/1.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.15/1.38          | ~ (v1_funct_1 @ X1))),
% 1.15/1.38      inference('demod', [status(thm)], ['79', '80'])).
% 1.15/1.38  thf('82', plain,
% 1.15/1.38      ((~ (v1_funct_1 @ sk_D)
% 1.15/1.38        | (m1_subset_1 @ 
% 1.15/1.38           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.15/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['76', '81'])).
% 1.15/1.38  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('84', plain,
% 1.15/1.38      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.38         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.15/1.38      inference('demod', [status(thm)], ['72', '73'])).
% 1.15/1.38  thf('85', plain,
% 1.15/1.38      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.15/1.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.38      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.15/1.38  thf(redefinition_r2_relset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.38     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.38       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.15/1.38  thf('86', plain,
% 1.15/1.38      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.15/1.38          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.15/1.38          | ((X39) = (X42))
% 1.15/1.38          | ~ (r2_relset_1 @ X40 @ X41 @ X39 @ X42))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.15/1.38  thf('87', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.15/1.38          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.15/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['85', '86'])).
% 1.15/1.38  thf('88', plain,
% 1.15/1.38      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.15/1.38        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['75', '87'])).
% 1.15/1.38  thf(dt_k6_partfun1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( m1_subset_1 @
% 1.15/1.38         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.15/1.38       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.15/1.38  thf('89', plain,
% 1.15/1.38      (![X50 : $i]:
% 1.15/1.38         (m1_subset_1 @ (k6_partfun1 @ X50) @ 
% 1.15/1.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.15/1.38  thf('90', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.38  thf(t182_relat_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( v1_relat_1 @ A ) =>
% 1.15/1.38       ( ![B:$i]:
% 1.15/1.38         ( ( v1_relat_1 @ B ) =>
% 1.15/1.38           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.15/1.38             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.15/1.38  thf('91', plain,
% 1.15/1.38      (![X11 : $i, X12 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X11)
% 1.15/1.38          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 1.15/1.38              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 1.15/1.38          | ~ (v1_relat_1 @ X12))),
% 1.15/1.38      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.15/1.38  thf('92', plain,
% 1.15/1.38      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.15/1.38          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup+', [status(thm)], ['90', '91'])).
% 1.15/1.38  thf(t71_relat_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.15/1.38       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.15/1.38  thf('93', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 1.15/1.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.15/1.38  thf('94', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('95', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 1.15/1.38      inference('demod', [status(thm)], ['93', '94'])).
% 1.15/1.38  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('98', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.15/1.38      inference('demod', [status(thm)], ['92', '95', '96', '97'])).
% 1.15/1.38  thf('99', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.15/1.38      inference('demod', [status(thm)], ['64', '98'])).
% 1.15/1.38  thf('100', plain,
% 1.15/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('101', plain,
% 1.15/1.38      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X33 @ X34)
% 1.15/1.38          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.15/1.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.38  thf('102', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.15/1.38      inference('sup-', [status(thm)], ['100', '101'])).
% 1.15/1.38  thf('103', plain,
% 1.15/1.38      (![X13 : $i, X14 : $i]:
% 1.15/1.38         (((X13) = (k7_relat_1 @ X13 @ X14))
% 1.15/1.38          | ~ (v4_relat_1 @ X13 @ X14)
% 1.15/1.38          | ~ (v1_relat_1 @ X13))),
% 1.15/1.38      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.15/1.38  thf('104', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['102', '103'])).
% 1.15/1.38  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('106', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['104', '105'])).
% 1.15/1.38  thf('107', plain,
% 1.15/1.38      (![X9 : $i, X10 : $i]:
% 1.15/1.38         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 1.15/1.38          | ~ (v1_relat_1 @ X9))),
% 1.15/1.38      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.15/1.38  thf('108', plain,
% 1.15/1.38      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['106', '107'])).
% 1.15/1.38  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('110', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['108', '109'])).
% 1.15/1.38  thf('111', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('112', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['110', '111'])).
% 1.15/1.38  thf('113', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup+', [status(thm)], ['99', '112'])).
% 1.15/1.38  thf('114', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 1.15/1.38      inference('demod', [status(thm)], ['44', '113'])).
% 1.15/1.38  thf('115', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.38  thf(dt_k2_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.38       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.15/1.38         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.15/1.38  thf('116', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('117', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('118', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf(t65_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.38       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.15/1.38  thf('119', plain,
% 1.15/1.38      (![X32 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X32)
% 1.15/1.38          | ((k2_funct_1 @ (k2_funct_1 @ X32)) = (X32))
% 1.15/1.38          | ~ (v1_funct_1 @ X32)
% 1.15/1.38          | ~ (v1_relat_1 @ X32))),
% 1.15/1.38      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.15/1.38  thf('120', plain,
% 1.15/1.38      (![X32 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X32)
% 1.15/1.38          | ((k2_funct_1 @ (k2_funct_1 @ X32)) = (X32))
% 1.15/1.38          | ~ (v1_funct_1 @ X32)
% 1.15/1.38          | ~ (v1_relat_1 @ X32))),
% 1.15/1.38      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.15/1.38  thf('121', plain,
% 1.15/1.38      (![X32 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X32)
% 1.15/1.38          | ((k2_funct_1 @ (k2_funct_1 @ X32)) = (X32))
% 1.15/1.38          | ~ (v1_funct_1 @ X32)
% 1.15/1.38          | ~ (v1_relat_1 @ X32))),
% 1.15/1.38      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.15/1.38  thf('122', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('123', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf(t55_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.38       ( ( v2_funct_1 @ A ) =>
% 1.15/1.38         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.15/1.38           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.15/1.38  thf('124', plain,
% 1.15/1.38      (![X30 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X30)
% 1.15/1.38          | ((k2_relat_1 @ X30) = (k1_relat_1 @ (k2_funct_1 @ X30)))
% 1.15/1.38          | ~ (v1_funct_1 @ X30)
% 1.15/1.38          | ~ (v1_relat_1 @ X30))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.38  thf('125', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('126', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('127', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('128', plain,
% 1.15/1.38      (![X30 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X30)
% 1.15/1.38          | ((k2_relat_1 @ X30) = (k1_relat_1 @ (k2_funct_1 @ X30)))
% 1.15/1.38          | ~ (v1_funct_1 @ X30)
% 1.15/1.38          | ~ (v1_relat_1 @ X30))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.38  thf('129', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.38      inference('simplify', [status(thm)], ['0'])).
% 1.15/1.38  thf('130', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.38          | (v4_relat_1 @ X5 @ X6)
% 1.15/1.38          | ~ (v1_relat_1 @ X5))),
% 1.15/1.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.38  thf('131', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['129', '130'])).
% 1.15/1.38  thf('132', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['128', '131'])).
% 1.15/1.38  thf('133', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['127', '132'])).
% 1.15/1.38  thf('134', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['133'])).
% 1.15/1.38  thf('135', plain,
% 1.15/1.38      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['126', '134'])).
% 1.15/1.38  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('139', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.15/1.38      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 1.15/1.38  thf('140', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.38          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.38          | ~ (v1_relat_1 @ X5))),
% 1.15/1.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.38  thf('141', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['139', '140'])).
% 1.15/1.38  thf('142', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['125', '141'])).
% 1.15/1.38  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('145', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.15/1.38      inference('demod', [status(thm)], ['142', '143', '144'])).
% 1.15/1.38  thf('146', plain,
% 1.15/1.38      (![X0 : $i, X2 : $i]:
% 1.15/1.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.15/1.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.38  thf('147', plain,
% 1.15/1.38      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['145', '146'])).
% 1.15/1.38  thf('148', plain,
% 1.15/1.38      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['124', '147'])).
% 1.15/1.38  thf('149', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('150', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.38      inference('simplify', [status(thm)], ['0'])).
% 1.15/1.38  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('154', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)],
% 1.15/1.38                ['148', '149', '150', '151', '152', '153'])).
% 1.15/1.38  thf('155', plain,
% 1.15/1.38      (![X30 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X30)
% 1.15/1.38          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 1.15/1.38          | ~ (v1_funct_1 @ X30)
% 1.15/1.38          | ~ (v1_relat_1 @ X30))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.38  thf('156', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('157', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf(t61_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.38       ( ( v2_funct_1 @ A ) =>
% 1.15/1.38         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.15/1.38             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.15/1.38           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.15/1.38             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.38  thf('158', plain,
% 1.15/1.38      (![X31 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X31)
% 1.15/1.38          | ((k5_relat_1 @ (k2_funct_1 @ X31) @ X31)
% 1.15/1.38              = (k6_relat_1 @ (k2_relat_1 @ X31)))
% 1.15/1.38          | ~ (v1_funct_1 @ X31)
% 1.15/1.38          | ~ (v1_relat_1 @ X31))),
% 1.15/1.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.38  thf('159', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('160', plain,
% 1.15/1.38      (![X31 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X31)
% 1.15/1.38          | ((k5_relat_1 @ (k2_funct_1 @ X31) @ X31)
% 1.15/1.38              = (k6_partfun1 @ (k2_relat_1 @ X31)))
% 1.15/1.38          | ~ (v1_funct_1 @ X31)
% 1.15/1.38          | ~ (v1_relat_1 @ X31))),
% 1.15/1.38      inference('demod', [status(thm)], ['158', '159'])).
% 1.15/1.38  thf(t48_funct_1, axiom,
% 1.15/1.38    (![A:$i]:
% 1.15/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.38       ( ![B:$i]:
% 1.15/1.38         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.15/1.38           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.15/1.38               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.15/1.38             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.15/1.38  thf('161', plain,
% 1.15/1.38      (![X28 : $i, X29 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X28)
% 1.15/1.38          | ~ (v1_funct_1 @ X28)
% 1.15/1.38          | (v2_funct_1 @ X28)
% 1.15/1.38          | ((k2_relat_1 @ X28) != (k1_relat_1 @ X29))
% 1.15/1.38          | ~ (v2_funct_1 @ (k5_relat_1 @ X28 @ X29))
% 1.15/1.38          | ~ (v1_funct_1 @ X29)
% 1.15/1.38          | ~ (v1_relat_1 @ X29))),
% 1.15/1.38      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.15/1.38  thf('162', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['160', '161'])).
% 1.15/1.38  thf('163', plain, (![X25 : $i]: (v2_funct_1 @ (k6_relat_1 @ X25))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.15/1.38  thf('164', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('165', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 1.15/1.38      inference('demod', [status(thm)], ['163', '164'])).
% 1.15/1.38  thf('166', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['162', '165'])).
% 1.15/1.38  thf('167', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['166'])).
% 1.15/1.38  thf('168', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['157', '167'])).
% 1.15/1.38  thf('169', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['168'])).
% 1.15/1.38  thf('170', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['156', '169'])).
% 1.15/1.38  thf('171', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['170'])).
% 1.15/1.38  thf('172', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['155', '171'])).
% 1.15/1.38  thf('173', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['172'])).
% 1.15/1.38  thf('174', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('175', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('176', plain,
% 1.15/1.38      (![X32 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X32)
% 1.15/1.38          | ((k2_funct_1 @ (k2_funct_1 @ X32)) = (X32))
% 1.15/1.38          | ~ (v1_funct_1 @ X32)
% 1.15/1.38          | ~ (v1_relat_1 @ X32))),
% 1.15/1.38      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.15/1.38  thf('177', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['133'])).
% 1.15/1.38  thf('178', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['176', '177'])).
% 1.15/1.38  thf('179', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['175', '178'])).
% 1.15/1.38  thf('180', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['179'])).
% 1.15/1.38  thf('181', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['174', '180'])).
% 1.15/1.38  thf('182', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['181'])).
% 1.15/1.38  thf('183', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['173', '182'])).
% 1.15/1.38  thf('184', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['183'])).
% 1.15/1.38  thf('185', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.38          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.38          | ~ (v1_relat_1 @ X5))),
% 1.15/1.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.38  thf('186', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['184', '185'])).
% 1.15/1.38  thf('187', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('simplify', [status(thm)], ['186'])).
% 1.15/1.38  thf('188', plain,
% 1.15/1.38      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['154', '187'])).
% 1.15/1.38  thf('189', plain,
% 1.15/1.38      (![X30 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X30)
% 1.15/1.38          | ((k2_relat_1 @ X30) = (k1_relat_1 @ (k2_funct_1 @ X30)))
% 1.15/1.38          | ~ (v1_funct_1 @ X30)
% 1.15/1.38          | ~ (v1_relat_1 @ X30))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.38  thf('190', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('191', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('192', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('193', plain,
% 1.15/1.38      (![X31 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X31)
% 1.15/1.38          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31))
% 1.15/1.38              = (k6_relat_1 @ (k1_relat_1 @ X31)))
% 1.15/1.38          | ~ (v1_funct_1 @ X31)
% 1.15/1.38          | ~ (v1_relat_1 @ X31))),
% 1.15/1.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.38  thf('194', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.38  thf('195', plain,
% 1.15/1.38      (![X31 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X31)
% 1.15/1.38          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31))
% 1.15/1.38              = (k6_partfun1 @ (k1_relat_1 @ X31)))
% 1.15/1.38          | ~ (v1_funct_1 @ X31)
% 1.15/1.38          | ~ (v1_relat_1 @ X31))),
% 1.15/1.38      inference('demod', [status(thm)], ['193', '194'])).
% 1.15/1.38  thf('196', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('197', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.38      inference('simplify', [status(thm)], ['0'])).
% 1.15/1.38  thf('198', plain,
% 1.15/1.38      (![X21 : $i, X22 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.15/1.38          | ((k5_relat_1 @ X21 @ (k6_partfun1 @ X22)) = (X21))
% 1.15/1.38          | ~ (v1_relat_1 @ X21))),
% 1.15/1.38      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.38  thf('199', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['197', '198'])).
% 1.15/1.38  thf('200', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['196', '199'])).
% 1.15/1.38  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('202', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['200', '201'])).
% 1.15/1.38  thf('203', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ X0 @ X1)
% 1.15/1.38              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.15/1.38                 (k5_relat_1 @ X0 @ X1))))),
% 1.15/1.38      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.38  thf('204', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.15/1.38          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['202', '203'])).
% 1.15/1.38  thf('205', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['200', '201'])).
% 1.15/1.38  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('207', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 1.15/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.15/1.38  thf('208', plain,
% 1.15/1.38      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 1.15/1.38  thf('209', plain,
% 1.15/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X15)
% 1.15/1.38          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 1.15/1.38              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 1.15/1.38          | ~ (v1_relat_1 @ X17)
% 1.15/1.38          | ~ (v1_relat_1 @ X16))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.38  thf('210', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k5_relat_1 @ sk_C @ X0)
% 1.15/1.38            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.15/1.38               (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['208', '209'])).
% 1.15/1.38  thf('211', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 1.15/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.15/1.38  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('213', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k5_relat_1 @ sk_C @ X0)
% 1.15/1.38            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.15/1.38               (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['210', '211', '212'])).
% 1.15/1.38  thf('214', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.15/1.38          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.15/1.38             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['195', '213'])).
% 1.15/1.38  thf('215', plain,
% 1.15/1.38      (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 1.15/1.38      inference('demod', [status(thm)], ['93', '94'])).
% 1.15/1.38  thf('216', plain,
% 1.15/1.38      (![X20 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X20)) @ X20) = (X20))
% 1.15/1.38          | ~ (v1_relat_1 @ X20))),
% 1.15/1.38      inference('demod', [status(thm)], ['30', '31'])).
% 1.15/1.38  thf('217', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.38            = (k6_partfun1 @ X0))
% 1.15/1.38          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['215', '216'])).
% 1.15/1.38  thf('218', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 1.15/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.15/1.38  thf('219', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.38           = (k6_partfun1 @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['217', '218'])).
% 1.15/1.38  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('223', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.15/1.38          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['214', '219', '220', '221', '222'])).
% 1.15/1.38  thf('224', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.15/1.38            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['192', '223'])).
% 1.15/1.38  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('227', plain,
% 1.15/1.38      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.15/1.38         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['224', '225', '226'])).
% 1.15/1.38  thf('228', plain,
% 1.15/1.38      (![X28 : $i, X29 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X28)
% 1.15/1.38          | ~ (v1_funct_1 @ X28)
% 1.15/1.38          | (v2_funct_1 @ X29)
% 1.15/1.38          | ((k2_relat_1 @ X28) != (k1_relat_1 @ X29))
% 1.15/1.38          | ~ (v2_funct_1 @ (k5_relat_1 @ X28 @ X29))
% 1.15/1.38          | ~ (v1_funct_1 @ X29)
% 1.15/1.38          | ~ (v1_relat_1 @ X29))),
% 1.15/1.38      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.15/1.38  thf('229', plain,
% 1.15/1.38      ((~ (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['227', '228'])).
% 1.15/1.38  thf('230', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 1.15/1.38      inference('demod', [status(thm)], ['163', '164'])).
% 1.15/1.38  thf('231', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('233', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('234', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['229', '230', '231', '232', '233'])).
% 1.15/1.38  thf('235', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['191', '234'])).
% 1.15/1.38  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('238', plain,
% 1.15/1.38      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['235', '236', '237'])).
% 1.15/1.38  thf('239', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['190', '238'])).
% 1.15/1.38  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('242', plain,
% 1.15/1.38      ((((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['239', '240', '241'])).
% 1.15/1.38  thf('243', plain,
% 1.15/1.38      ((((sk_B) != (k2_relat_1 @ sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['189', '242'])).
% 1.15/1.38  thf('244', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('248', plain,
% 1.15/1.38      ((((sk_B) != (sk_B)) | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['243', '244', '245', '246', '247'])).
% 1.15/1.38  thf('249', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('simplify', [status(thm)], ['248'])).
% 1.15/1.38  thf('250', plain,
% 1.15/1.38      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['188', '249'])).
% 1.15/1.38  thf('251', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['123', '250'])).
% 1.15/1.38  thf('252', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('254', plain,
% 1.15/1.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.15/1.38      inference('demod', [status(thm)], ['251', '252', '253'])).
% 1.15/1.38  thf('255', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['122', '254'])).
% 1.15/1.38  thf('256', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('257', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('258', plain,
% 1.15/1.38      ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.38      inference('demod', [status(thm)], ['255', '256', '257'])).
% 1.15/1.38  thf('259', plain,
% 1.15/1.38      (![X0 : $i, X2 : $i]:
% 1.15/1.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.15/1.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.38  thf('260', plain,
% 1.15/1.38      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)
% 1.15/1.38        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['258', '259'])).
% 1.15/1.38  thf('261', plain,
% 1.15/1.38      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['121', '260'])).
% 1.15/1.38  thf('262', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['52', '53'])).
% 1.15/1.38  thf('263', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.38      inference('simplify', [status(thm)], ['0'])).
% 1.15/1.38  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('265', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('266', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('267', plain,
% 1.15/1.38      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 1.15/1.38      inference('demod', [status(thm)],
% 1.15/1.38                ['261', '262', '263', '264', '265', '266'])).
% 1.15/1.38  thf('268', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['197', '198'])).
% 1.15/1.38  thf('269', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.15/1.38          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.38      inference('sup+', [status(thm)], ['267', '268'])).
% 1.15/1.38  thf('270', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.15/1.38            (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['120', '269'])).
% 1.15/1.38  thf('271', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('272', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('273', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('274', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('275', plain,
% 1.15/1.38      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 1.15/1.38         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['270', '271', '272', '273', '274'])).
% 1.15/1.38  thf('276', plain,
% 1.15/1.38      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.15/1.38          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['119', '275'])).
% 1.15/1.38  thf('277', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['200', '201'])).
% 1.15/1.38  thf('278', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('279', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('280', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('281', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['276', '277', '278', '279', '280'])).
% 1.15/1.38  thf('282', plain,
% 1.15/1.38      (![X31 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X31)
% 1.15/1.38          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31))
% 1.15/1.38              = (k6_partfun1 @ (k1_relat_1 @ X31)))
% 1.15/1.38          | ~ (v1_funct_1 @ X31)
% 1.15/1.38          | ~ (v1_relat_1 @ X31))),
% 1.15/1.38      inference('demod', [status(thm)], ['193', '194'])).
% 1.15/1.38  thf('283', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.15/1.38          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['281', '282'])).
% 1.15/1.38  thf('284', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)],
% 1.15/1.38                ['148', '149', '150', '151', '152', '153'])).
% 1.15/1.38  thf('285', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('simplify', [status(thm)], ['248'])).
% 1.15/1.38  thf('286', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['283', '284', '285'])).
% 1.15/1.38  thf('287', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['118', '286'])).
% 1.15/1.38  thf('288', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('289', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('290', plain,
% 1.15/1.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.15/1.38      inference('demod', [status(thm)], ['287', '288', '289'])).
% 1.15/1.38  thf('291', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['117', '290'])).
% 1.15/1.38  thf('292', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('293', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('294', plain,
% 1.15/1.38      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['291', '292', '293'])).
% 1.15/1.38  thf('295', plain,
% 1.15/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X15)
% 1.15/1.38          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 1.15/1.38              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 1.15/1.38          | ~ (v1_relat_1 @ X17)
% 1.15/1.38          | ~ (v1_relat_1 @ X16))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.38  thf('296', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.38            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['294', '295'])).
% 1.15/1.38  thf('297', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('298', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.38            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38          | ~ (v1_relat_1 @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['296', '297'])).
% 1.15/1.38  thf('299', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ sk_C)
% 1.15/1.38          | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.38              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.15/1.38      inference('sup-', [status(thm)], ['116', '298'])).
% 1.15/1.38  thf('300', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('301', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('302', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (~ (v1_relat_1 @ X0)
% 1.15/1.38          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.38              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.15/1.38      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.15/1.38  thf('303', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.15/1.38          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.15/1.38        | ~ (v1_relat_1 @ sk_D))),
% 1.15/1.38      inference('sup+', [status(thm)], ['115', '302'])).
% 1.15/1.38  thf('304', plain,
% 1.15/1.38      (![X23 : $i]:
% 1.15/1.38         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 1.15/1.38          | ~ (v1_funct_1 @ X23)
% 1.15/1.38          | ~ (v1_relat_1 @ X23))),
% 1.15/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.38  thf('305', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.15/1.38      inference('sup-', [status(thm)], ['100', '101'])).
% 1.15/1.38  thf('306', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.38          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.38          | ~ (v1_relat_1 @ X5))),
% 1.15/1.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.38  thf('307', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.15/1.38      inference('sup-', [status(thm)], ['305', '306'])).
% 1.15/1.38  thf('308', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('309', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.15/1.38      inference('demod', [status(thm)], ['307', '308'])).
% 1.15/1.38  thf('310', plain,
% 1.15/1.38      (![X30 : $i]:
% 1.15/1.38         (~ (v2_funct_1 @ X30)
% 1.15/1.38          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 1.15/1.38          | ~ (v1_funct_1 @ X30)
% 1.15/1.38          | ~ (v1_relat_1 @ X30))),
% 1.15/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.38  thf('311', plain,
% 1.15/1.38      (![X21 : $i, X22 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.15/1.38          | ((k5_relat_1 @ X21 @ (k6_partfun1 @ X22)) = (X21))
% 1.15/1.38          | ~ (v1_relat_1 @ X21))),
% 1.15/1.38      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.38  thf('312', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.15/1.38          | ~ (v1_relat_1 @ X0)
% 1.15/1.38          | ~ (v1_funct_1 @ X0)
% 1.15/1.38          | ~ (v2_funct_1 @ X0)
% 1.15/1.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.15/1.38          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 1.15/1.38              = (k2_funct_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['310', '311'])).
% 1.15/1.38  thf('313', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.38          = (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.38      inference('sup-', [status(thm)], ['309', '312'])).
% 1.15/1.38  thf('314', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('316', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('317', plain,
% 1.15/1.38      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.38          = (k2_funct_1 @ sk_C))
% 1.15/1.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('demod', [status(thm)], ['313', '314', '315', '316'])).
% 1.15/1.38  thf('318', plain,
% 1.15/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.38        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.38            = (k2_funct_1 @ sk_C)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['304', '317'])).
% 1.15/1.38  thf('319', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf('320', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('321', plain,
% 1.15/1.38      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.38         = (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['318', '319', '320'])).
% 1.15/1.38  thf('322', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.38      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.38  thf('323', plain,
% 1.15/1.38      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('demod', [status(thm)], ['303', '321', '322'])).
% 1.15/1.38  thf('324', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('sup+', [status(thm)], ['114', '323'])).
% 1.15/1.38  thf('325', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('326', plain, ($false),
% 1.15/1.38      inference('simplify_reflect-', [status(thm)], ['324', '325'])).
% 1.15/1.38  
% 1.15/1.38  % SZS output end Refutation
% 1.15/1.38  
% 1.15/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
