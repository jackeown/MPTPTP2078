%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VyQIKQdMxQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 299 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  767 (4787 expanded)
%              Number of equality atoms :   57 ( 223 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('11',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ X13 )
      | ( ( k3_funct_2 @ X13 @ X14 @ X12 @ X15 )
        = ( k1_funct_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf('39',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ X6 ) )
       != ( sk_C @ X7 @ X6 ) )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('42',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('44',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','50'])).

thf('52',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['52','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VyQIKQdMxQ
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:18 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 38 iterations in 0.021s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(t201_funct_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48           ( ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.48                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.48             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48              ( ( ![C:$i]:
% 0.22/0.48                  ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.48                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.48                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.22/0.48  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t67_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X21 : $i, X22 : $i]:
% 0.22/0.48         (((k1_relset_1 @ X21 @ X21 @ X22) = (X21))
% 0.22/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.22/0.48          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.22/0.48          | ~ (v1_funct_1 @ X22))),
% 0.22/0.48      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.48        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.48        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.48         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.22/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.48  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf(t34_funct_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.48       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.22/0.48         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (((k1_relat_1 @ X7) != (X6))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 0.22/0.48          | ((X7) = (k6_relat_1 @ X6))
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ~ (v1_relat_1 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X7 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X7)
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.48  thf('12', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X7 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X7)
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.22/0.48          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup+', [status(thm)], ['9', '13'])).
% 0.22/0.48  thf('15', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf('16', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(cc2_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.22/0.48          | (v1_relat_1 @ X2)
% 0.22/0.48          | ~ (v1_relat_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf(fc6_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.48  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '15', '16', '17', '22'])).
% 0.22/0.48  thf(t1_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X23 : $i]:
% 0.22/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X23) = (X23))
% 0.22/0.48          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.48            = (sk_C @ sk_B @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.22/0.48          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.22/0.48          | ~ (v1_funct_1 @ X12)
% 0.22/0.48          | (v1_xboole_0 @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ X13)
% 0.22/0.48          | ((k3_funct_2 @ X13 @ X14 @ X12 @ X15) = (k1_funct_1 @ X12 @ X15)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.48          | (v1_xboole_0 @ sk_A)
% 0.22/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.48  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('33', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.48          | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.48  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.48          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.22/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.48            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['28', '36'])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['27', '37'])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.48        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.48  thf('40', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (((k1_relat_1 @ X7) != (X6))
% 0.22/0.48          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ X6)) != (sk_C @ X7 @ X6))
% 0.22/0.48          | ((X7) = (k6_relat_1 @ X6))
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ~ (v1_relat_1 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.48  thf('42', plain,
% 0.22/0.48      (![X7 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X7)
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.22/0.48          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.22/0.48              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.48  thf('43', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      (![X7 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X7)
% 0.22/0.48          | ~ (v1_funct_1 @ X7)
% 0.22/0.48          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.22/0.48          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.22/0.48              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.22/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.48  thf('45', plain,
% 0.22/0.48      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.48          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['40', '44'])).
% 0.22/0.48  thf('46', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf('47', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.22/0.48  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('50', plain,
% 0.22/0.48      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.22/0.48        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.22/0.48  thf('51', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['39', '50'])).
% 0.22/0.48  thf('52', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '51'])).
% 0.22/0.48  thf('53', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_r2_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.48  thf('54', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.48          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.22/0.48          | ~ (v1_funct_1 @ X17)
% 0.22/0.48          | ~ (v1_funct_1 @ X20)
% 0.22/0.48          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.48          | (r2_funct_2 @ X18 @ X19 @ X17 @ X20)
% 0.22/0.48          | ((X17) != (X20)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.22/0.48  thf('55', plain,
% 0.22/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.22/0.48          | ~ (v1_funct_1 @ X20)
% 0.22/0.48          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.48  thf('56', plain,
% 0.22/0.48      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['53', '55'])).
% 0.22/0.48  thf('57', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('59', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.22/0.48  thf('60', plain, ($false), inference('demod', [status(thm)], ['52', '59'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
