%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsEJM59BAW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 290 expanded)
%              Number of leaves         :   27 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  760 (4759 expanded)
%              Number of equality atoms :   57 ( 223 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X20 @ X21 )
        = X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
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
    ! [X22: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ X12 )
      | ( ( k3_funct_2 @ X12 @ X13 @ X11 @ X14 )
        = ( k1_funct_1 @ X11 @ X14 ) ) ) ),
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
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
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

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_funct_2 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['50','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsEJM59BAW
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 37 iterations in 0.021s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(t201_funct_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46           ( ( ![C:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.46                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.46             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46              ( ( ![C:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.46                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.46                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.20/0.46  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t67_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X20 : $i, X21 : $i]:
% 0.20/0.46         (((k1_relset_1 @ X20 @ X20 @ X21) = (X20))
% 0.20/0.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.20/0.46          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.20/0.46          | ~ (v1_funct_1 @ X21))),
% 0.20/0.46      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.46        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.46         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.20/0.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.46  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf(t34_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.46         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((k1_relat_1 @ X3) != (X2))
% 0.20/0.46          | (r2_hidden @ (sk_C @ X3 @ X2) @ X2)
% 0.20/0.46          | ((X3) = (k6_relat_1 @ X2))
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X3 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X3)
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.20/0.46          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('12', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X3 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X3)
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.20/0.46          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf(t1_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.46        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['9', '15'])).
% 0.20/0.46  thf('17', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( v1_relat_1 @ C ) ))).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((v1_relat_1 @ X5)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.46  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('22', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17', '20', '21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (![X22 : $i]:
% 0.20/0.46         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X22) = (X22))
% 0.20/0.46          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.46        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.46            = (sk_C @ sk_B @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17', '20', '21', '22'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.46         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.46       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.46          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.20/0.46          | ~ (v1_funct_1 @ X11)
% 0.20/0.46          | (v1_xboole_0 @ X12)
% 0.20/0.46          | ~ (m1_subset_1 @ X14 @ X12)
% 0.20/0.46          | ((k3_funct_2 @ X12 @ X13 @ X11 @ X14) = (k1_funct_1 @ X11 @ X14)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.46          | (v1_xboole_0 @ sk_A)
% 0.20/0.46          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('31', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.46          | (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.46  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.46          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.46      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.46        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.46            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '34'])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['25', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.46        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.46  thf('38', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((k1_relat_1 @ X3) != (X2))
% 0.20/0.46          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ X2)) != (sk_C @ X3 @ X2))
% 0.20/0.46          | ((X3) = (k6_relat_1 @ X2))
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.46  thf('40', plain,
% 0.20/0.46      (![X3 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X3)
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.20/0.46          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.20/0.46              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.46  thf('41', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('42', plain,
% 0.20/0.46      (![X3 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X3)
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.20/0.46          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.20/0.46              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.20/0.46      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.46  thf('43', plain,
% 0.20/0.46      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.46          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.20/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['38', '42'])).
% 0.20/0.46  thf('44', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf('45', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.46  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('48', plain,
% 0.20/0.46      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.20/0.46        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.20/0.46  thf('49', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.20/0.46      inference('clc', [status(thm)], ['37', '48'])).
% 0.20/0.46  thf('50', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '49'])).
% 0.20/0.46  thf('51', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_r2_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.46  thf('52', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.46          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.20/0.46          | ~ (v1_funct_1 @ X16)
% 0.20/0.46          | ~ (v1_funct_1 @ X19)
% 0.20/0.46          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.20/0.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.46          | (r2_funct_2 @ X17 @ X18 @ X16 @ X19)
% 0.20/0.46          | ((X16) != (X19)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.20/0.46  thf('53', plain,
% 0.20/0.46      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.46         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.20/0.46          | ~ (v1_funct_1 @ X19)
% 0.20/0.46          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.20/0.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.46  thf('54', plain,
% 0.20/0.46      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.46  thf('55', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('57', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.46  thf('58', plain, ($false), inference('demod', [status(thm)], ['50', '57'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
