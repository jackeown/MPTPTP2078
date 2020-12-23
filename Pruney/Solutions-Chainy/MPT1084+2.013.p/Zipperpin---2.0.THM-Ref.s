%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qRxifZwrU2

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 (1470 expanded)
%              Number of leaves         :   28 ( 454 expanded)
%              Depth                    :   20
%              Number of atoms          : 1077 (25882 expanded)
%              Number of equality atoms :   65 (1177 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t201_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( k3_funct_2 @ A @ A @ B @ C )
                  = C ) )
           => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ A )
                 => ( ( k3_funct_2 @ A @ A @ B @ C )
                    = C ) )
             => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_funct_2])).

thf('0',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X21 @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('11',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','20','21','22'])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','20','21','22'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ X17 )
      | ( ( k3_funct_2 @ X17 @ X18 @ X16 @ X19 )
        = ( k1_funct_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ X2 ) )
       != ( sk_C @ X3 @ X2 ) )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('40',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','48'])).

thf('50',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X11 @ X14 @ X12 ) @ X12 )
      | ( r2_funct_2 @ X12 @ X13 @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','49'])).

thf('64',plain,(
    m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('66',plain,
    ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('68',plain,(
    ! [X23: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k1_funct_1 @ X14 @ ( sk_E @ X11 @ X14 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_E @ X11 @ X14 @ X12 ) ) )
      | ( r2_funct_2 @ X12 @ X13 @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_B @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_B @ sk_B @ sk_A )
       != ( sk_E @ sk_B @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['50','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qRxifZwrU2
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 45 iterations in 0.023s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.22/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.22/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.47  thf(t201_funct_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.47           ( ( ![C:$i]:
% 0.22/0.47               ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.47                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.47             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.47              ( ( ![C:$i]:
% 0.22/0.47                  ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.47                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.47                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.22/0.47  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t67_funct_2, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.47       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X21 : $i, X22 : $i]:
% 0.22/0.47         (((k1_relset_1 @ X21 @ X21 @ X22) = (X21))
% 0.22/0.47          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.22/0.47          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.22/0.47          | ~ (v1_funct_1 @ X22))),
% 0.22/0.47      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.47        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.47        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.47         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.22/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.47  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf(t34_funct_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.47       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.22/0.47         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         (((k1_relat_1 @ X3) != (X2))
% 0.22/0.47          | (r2_hidden @ (sk_C @ X3 @ X2) @ X2)
% 0.22/0.47          | ((X3) = (k6_relat_1 @ X2))
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X3)
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.22/0.47          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.47  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.47  thf('12', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X3)
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.22/0.47          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.47  thf(t1_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '15'])).
% 0.22/0.47  thf('17', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(cc1_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( v1_relat_1 @ C ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.47         ((v1_relat_1 @ X5)
% 0.22/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('22', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['16', '17', '20', '21', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X23 : $i]:
% 0.22/0.47         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23) = (X23))
% 0.22/0.47          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.47        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47            = (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['16', '17', '20', '21', '22'])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.47         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.47         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.47       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.47          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.22/0.47          | ~ (v1_funct_1 @ X16)
% 0.22/0.47          | (v1_xboole_0 @ X17)
% 0.22/0.47          | ~ (m1_subset_1 @ X19 @ X17)
% 0.22/0.47          | ((k3_funct_2 @ X17 @ X18 @ X16 @ X19) = (k1_funct_1 @ X16 @ X19)))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.47          | (v1_xboole_0 @ sk_A)
% 0.22/0.47          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.47  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('31', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('32', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.47          | (v1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.47  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.47          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.22/0.47      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.47  thf('35', plain,
% 0.22/0.47      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.47        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['26', '34'])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.47      inference('sup+', [status(thm)], ['25', '35'])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.47        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.47  thf('38', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf('39', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         (((k1_relat_1 @ X3) != (X2))
% 0.22/0.47          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ X2)) != (sk_C @ X3 @ X2))
% 0.22/0.47          | ((X3) = (k6_relat_1 @ X2))
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.47  thf('40', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X3)
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.22/0.47          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.22/0.47              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.22/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.47  thf('41', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.47  thf('42', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X3)
% 0.22/0.47          | ~ (v1_funct_1 @ X3)
% 0.22/0.47          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.22/0.47          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.22/0.47              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.22/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.47  thf('43', plain,
% 0.22/0.47      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['38', '42'])).
% 0.22/0.47  thf('44', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf('45', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.47  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('48', plain,
% 0.22/0.47      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.22/0.47  thf('49', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['37', '48'])).
% 0.22/0.47  thf('50', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '49'])).
% 0.22/0.47  thf('51', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('52', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('53', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d9_funct_2, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.47       ( ![D:$i]:
% 0.22/0.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.47           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.22/0.47             ( ![E:$i]:
% 0.22/0.47               ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.47                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('54', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X11)
% 0.22/0.47          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.22/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.47          | (m1_subset_1 @ (sk_E @ X11 @ X14 @ X12) @ X12)
% 0.22/0.47          | (r2_funct_2 @ X12 @ X13 @ X14 @ X11)
% 0.22/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.47          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.22/0.47          | ~ (v1_funct_1 @ X14))),
% 0.22/0.47      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.22/0.47  thf('55', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.47          | (r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.22/0.47          | (m1_subset_1 @ (sk_E @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.47          | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.47  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('58', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.47          | (r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.22/0.47          | (m1_subset_1 @ (sk_E @ sk_B @ X0 @ sk_A) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.22/0.47  thf('59', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)
% 0.22/0.47        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['52', '58'])).
% 0.22/0.47  thf('60', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('62', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.22/0.47  thf('63', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '49'])).
% 0.22/0.47  thf('64', plain, ((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.47  thf('65', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.47          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.22/0.47      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.47  thf('66', plain,
% 0.22/0.47      (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.22/0.47         = (k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.47  thf('67', plain, ((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.47  thf('68', plain,
% 0.22/0.47      (![X23 : $i]:
% 0.22/0.47         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23) = (X23))
% 0.22/0.47          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('69', plain,
% 0.22/0.47      (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.22/0.47         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.47  thf('70', plain,
% 0.22/0.47      (((k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.22/0.47         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.22/0.47      inference('sup+', [status(thm)], ['66', '69'])).
% 0.22/0.47  thf('71', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X11)
% 0.22/0.47          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.22/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.47          | ((k1_funct_1 @ X14 @ (sk_E @ X11 @ X14 @ X12))
% 0.22/0.47              != (k1_funct_1 @ X11 @ (sk_E @ X11 @ X14 @ X12)))
% 0.22/0.47          | (r2_funct_2 @ X12 @ X13 @ X14 @ X11)
% 0.22/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.47          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.22/0.47          | ~ (v1_funct_1 @ X14))),
% 0.22/0.47      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.22/0.47  thf('72', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((sk_E @ sk_B @ sk_B @ sk_A)
% 0.22/0.47            != (k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A)))
% 0.22/0.47          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.47          | (r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.22/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.22/0.47          | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.47  thf('73', plain,
% 0.22/0.47      (((k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.22/0.47         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.22/0.47      inference('sup+', [status(thm)], ['66', '69'])).
% 0.22/0.47  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('76', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((sk_E @ sk_B @ sk_B @ sk_A) != (sk_E @ sk_B @ sk_B @ sk_A))
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.47          | (r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.22/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.22/0.47  thf('77', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.22/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.47          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.47  thf('78', plain,
% 0.22/0.47      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.47        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['51', '77'])).
% 0.22/0.47  thf('79', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('80', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.47      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.47  thf('81', plain, ($false), inference('demod', [status(thm)], ['50', '80'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
