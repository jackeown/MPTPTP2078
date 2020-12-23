%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NQpJbVIxiw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:41 EST 2020

% Result     : Theorem 49.25s
% Output     : Refutation 49.25s
% Verified   : 
% Statistics : Number of formulae       :  217 (3071 expanded)
%              Number of leaves         :   40 ( 888 expanded)
%              Depth                    :   29
%              Number of atoms          : 1763 (50450 expanded)
%              Number of equality atoms :  168 (3317 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X35 @ X36 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 )
        = ( k7_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X35 @ X36 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('67',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('69',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('77',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('100',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','96','97','108','109'])).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 )
        = ( k7_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('112',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
          = ( k7_relat_1 @ sk_D @ X2 ) )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('117',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('119',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('122',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('124',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('125',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('126',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('127',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('128',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('129',plain,
    ( ! [X0: $i,X1: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','96','97','108','109'])).

thf('130',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('131',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('133',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('135',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ X1 )
        | ( v1_funct_2 @ sk_D @ X1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('138',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('139',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['140','142'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','144'])).

thf('146',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['117','122','123','124','125','126','127','128','145'])).

thf('147',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('148',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['146','147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','149'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['153'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('155',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('161',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('167',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','148'])).

thf('171',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','171'])).

thf('173',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['159','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['38','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NQpJbVIxiw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 49.25/49.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 49.25/49.49  % Solved by: fo/fo7.sh
% 49.25/49.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.25/49.49  % done 17309 iterations in 49.025s
% 49.25/49.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 49.25/49.49  % SZS output start Refutation
% 49.25/49.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 49.25/49.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 49.25/49.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 49.25/49.49  thf(sk_C_type, type, sk_C: $i).
% 49.25/49.49  thf(sk_D_type, type, sk_D: $i).
% 49.25/49.49  thf(sk_A_type, type, sk_A: $i).
% 49.25/49.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 49.25/49.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 49.25/49.49  thf(sk_B_type, type, sk_B: $i).
% 49.25/49.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 49.25/49.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 49.25/49.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 49.25/49.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 49.25/49.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 49.25/49.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 49.25/49.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 49.25/49.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 49.25/49.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 49.25/49.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 49.25/49.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 49.25/49.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 49.25/49.49  thf(t38_funct_2, conjecture,
% 49.25/49.49    (![A:$i,B:$i,C:$i,D:$i]:
% 49.25/49.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 49.25/49.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 49.25/49.49       ( ( r1_tarski @ C @ A ) =>
% 49.25/49.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 49.25/49.49           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 49.25/49.49             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 49.25/49.49             ( m1_subset_1 @
% 49.25/49.49               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 49.25/49.49               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 49.25/49.49  thf(zf_stmt_0, negated_conjecture,
% 49.25/49.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 49.25/49.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 49.25/49.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 49.25/49.49          ( ( r1_tarski @ C @ A ) =>
% 49.25/49.49            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 49.25/49.49              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 49.25/49.49                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 49.25/49.49                ( m1_subset_1 @
% 49.25/49.49                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 49.25/49.49                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 49.25/49.49    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 49.25/49.49  thf('0', plain,
% 49.25/49.49      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 49.25/49.49        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 49.25/49.49             sk_B)
% 49.25/49.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('1', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf(dt_k2_partfun1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i,D:$i]:
% 49.25/49.49     ( ( ( v1_funct_1 @ C ) & 
% 49.25/49.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 49.25/49.49       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 49.25/49.49         ( m1_subset_1 @
% 49.25/49.49           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 49.25/49.49           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 49.25/49.49  thf('2', plain,
% 49.25/49.49      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 49.25/49.49          | ~ (v1_funct_1 @ X34)
% 49.25/49.49          | (v1_funct_1 @ (k2_partfun1 @ X35 @ X36 @ X34 @ X37)))),
% 49.25/49.49      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 49.25/49.49  thf('3', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 49.25/49.49          | ~ (v1_funct_1 @ sk_D))),
% 49.25/49.49      inference('sup-', [status(thm)], ['1', '2'])).
% 49.25/49.49  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('5', plain,
% 49.25/49.49      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 49.25/49.49      inference('demod', [status(thm)], ['3', '4'])).
% 49.25/49.49  thf('6', plain,
% 49.25/49.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 49.25/49.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 49.25/49.49      inference('demod', [status(thm)], ['0', '5'])).
% 49.25/49.49  thf('7', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf(redefinition_k2_partfun1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i,D:$i]:
% 49.25/49.49     ( ( ( v1_funct_1 @ C ) & 
% 49.25/49.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 49.25/49.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 49.25/49.49  thf('8', plain,
% 49.25/49.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 49.25/49.49          | ~ (v1_funct_1 @ X38)
% 49.25/49.49          | ((k2_partfun1 @ X39 @ X40 @ X38 @ X41) = (k7_relat_1 @ X38 @ X41)))),
% 49.25/49.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 49.25/49.49  thf('9', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 49.25/49.49          | ~ (v1_funct_1 @ sk_D))),
% 49.25/49.49      inference('sup-', [status(thm)], ['7', '8'])).
% 49.25/49.49  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('11', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 49.25/49.49      inference('demod', [status(thm)], ['9', '10'])).
% 49.25/49.49  thf('12', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 49.25/49.49      inference('demod', [status(thm)], ['9', '10'])).
% 49.25/49.49  thf('13', plain,
% 49.25/49.49      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 49.25/49.49        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 49.25/49.49      inference('demod', [status(thm)], ['6', '11', '12'])).
% 49.25/49.49  thf('14', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('15', plain,
% 49.25/49.49      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 49.25/49.49          | ~ (v1_funct_1 @ X34)
% 49.25/49.49          | (m1_subset_1 @ (k2_partfun1 @ X35 @ X36 @ X34 @ X37) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 49.25/49.49      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 49.25/49.49  thf('16', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 49.25/49.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 49.25/49.49          | ~ (v1_funct_1 @ sk_D))),
% 49.25/49.49      inference('sup-', [status(thm)], ['14', '15'])).
% 49.25/49.49  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('18', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['16', '17'])).
% 49.25/49.49  thf('19', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 49.25/49.49      inference('demod', [status(thm)], ['9', '10'])).
% 49.25/49.49  thf('20', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['18', '19'])).
% 49.25/49.49  thf(cc2_relset_1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.25/49.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 49.25/49.49  thf('21', plain,
% 49.25/49.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 49.25/49.49         ((v5_relat_1 @ X17 @ X19)
% 49.25/49.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 49.25/49.49  thf('22', plain,
% 49.25/49.49      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 49.25/49.49      inference('sup-', [status(thm)], ['20', '21'])).
% 49.25/49.49  thf(d19_relat_1, axiom,
% 49.25/49.49    (![A:$i,B:$i]:
% 49.25/49.49     ( ( v1_relat_1 @ B ) =>
% 49.25/49.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 49.25/49.49  thf('23', plain,
% 49.25/49.49      (![X4 : $i, X5 : $i]:
% 49.25/49.49         (~ (v5_relat_1 @ X4 @ X5)
% 49.25/49.49          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 49.25/49.49          | ~ (v1_relat_1 @ X4))),
% 49.25/49.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 49.25/49.49  thf('24', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 49.25/49.49          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 49.25/49.49      inference('sup-', [status(thm)], ['22', '23'])).
% 49.25/49.49  thf('25', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['18', '19'])).
% 49.25/49.49  thf(cc1_relset_1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.25/49.49       ( v1_relat_1 @ C ) ))).
% 49.25/49.49  thf('26', plain,
% 49.25/49.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 49.25/49.49         ((v1_relat_1 @ X14)
% 49.25/49.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 49.25/49.49  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['25', '26'])).
% 49.25/49.49  thf('28', plain,
% 49.25/49.49      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 49.25/49.49      inference('demod', [status(thm)], ['24', '27'])).
% 49.25/49.49  thf(t87_relat_1, axiom,
% 49.25/49.49    (![A:$i,B:$i]:
% 49.25/49.49     ( ( v1_relat_1 @ B ) =>
% 49.25/49.49       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 49.25/49.49  thf('29', plain,
% 49.25/49.49      (![X10 : $i, X11 : $i]:
% 49.25/49.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 49.25/49.49          | ~ (v1_relat_1 @ X10))),
% 49.25/49.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 49.25/49.49  thf(t11_relset_1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( v1_relat_1 @ C ) =>
% 49.25/49.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 49.25/49.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 49.25/49.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 49.25/49.49  thf('30', plain,
% 49.25/49.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 49.25/49.49         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 49.25/49.49          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 49.25/49.49          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 49.25/49.49          | ~ (v1_relat_1 @ X23))),
% 49.25/49.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 49.25/49.49  thf('31', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.25/49.49         (~ (v1_relat_1 @ X1)
% 49.25/49.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 49.25/49.49          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 49.25/49.49          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 49.25/49.49      inference('sup-', [status(thm)], ['29', '30'])).
% 49.25/49.49  thf('32', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 49.25/49.49          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 49.25/49.49          | ~ (v1_relat_1 @ sk_D))),
% 49.25/49.49      inference('sup-', [status(thm)], ['28', '31'])).
% 49.25/49.49  thf('33', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['25', '26'])).
% 49.25/49.49  thf('34', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('35', plain,
% 49.25/49.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 49.25/49.49         ((v1_relat_1 @ X14)
% 49.25/49.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 49.25/49.49  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('37', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['32', '33', '36'])).
% 49.25/49.49  thf('38', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 49.25/49.49      inference('demod', [status(thm)], ['13', '37'])).
% 49.25/49.49  thf('39', plain, ((r1_tarski @ sk_C @ sk_A)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf(d1_funct_2, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.25/49.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 49.25/49.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 49.25/49.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 49.25/49.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 49.25/49.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 49.25/49.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 49.25/49.49  thf(zf_stmt_1, axiom,
% 49.25/49.49    (![B:$i,A:$i]:
% 49.25/49.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 49.25/49.49       ( zip_tseitin_0 @ B @ A ) ))).
% 49.25/49.49  thf('40', plain,
% 49.25/49.49      (![X26 : $i, X27 : $i]:
% 49.25/49.49         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 49.25/49.49  thf(t113_zfmisc_1, axiom,
% 49.25/49.49    (![A:$i,B:$i]:
% 49.25/49.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 49.25/49.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 49.25/49.49  thf('41', plain,
% 49.25/49.49      (![X2 : $i, X3 : $i]:
% 49.25/49.49         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 49.25/49.49  thf('42', plain,
% 49.25/49.49      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['41'])).
% 49.25/49.49  thf('43', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.25/49.49         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 49.25/49.49      inference('sup+', [status(thm)], ['40', '42'])).
% 49.25/49.49  thf('44', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 49.25/49.49  thf(zf_stmt_3, axiom,
% 49.25/49.49    (![C:$i,B:$i,A:$i]:
% 49.25/49.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 49.25/49.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 49.25/49.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 49.25/49.49  thf(zf_stmt_5, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.25/49.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 49.25/49.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 49.25/49.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 49.25/49.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 49.25/49.49  thf('45', plain,
% 49.25/49.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 49.25/49.49         (~ (zip_tseitin_0 @ X31 @ X32)
% 49.25/49.49          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 49.25/49.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 49.25/49.49  thf('46', plain,
% 49.25/49.49      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 49.25/49.49      inference('sup-', [status(thm)], ['44', '45'])).
% 49.25/49.49  thf('47', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 49.25/49.49          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 49.25/49.49      inference('sup-', [status(thm)], ['43', '46'])).
% 49.25/49.49  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('49', plain,
% 49.25/49.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 49.25/49.49         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 49.25/49.49          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 49.25/49.49          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 49.25/49.49  thf('50', plain,
% 49.25/49.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 49.25/49.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['48', '49'])).
% 49.25/49.49  thf('51', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf(redefinition_k1_relset_1, axiom,
% 49.25/49.49    (![A:$i,B:$i,C:$i]:
% 49.25/49.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 49.25/49.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 49.25/49.49  thf('52', plain,
% 49.25/49.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 49.25/49.49         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 49.25/49.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 49.25/49.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 49.25/49.49  thf('53', plain,
% 49.25/49.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 49.25/49.49      inference('sup-', [status(thm)], ['51', '52'])).
% 49.25/49.49  thf('54', plain,
% 49.25/49.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('demod', [status(thm)], ['50', '53'])).
% 49.25/49.49  thf('55', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 49.25/49.49          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['47', '54'])).
% 49.25/49.49  thf('56', plain,
% 49.25/49.49      (![X1 : $i, X2 : $i]:
% 49.25/49.49         (((X1) = (k1_xboole_0))
% 49.25/49.49          | ((X2) = (k1_xboole_0))
% 49.25/49.49          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 49.25/49.49  thf('57', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((k1_xboole_0) != (k1_xboole_0))
% 49.25/49.49          | ((sk_A) = (k1_relat_1 @ sk_D))
% 49.25/49.49          | ((sk_B) = (k1_xboole_0))
% 49.25/49.49          | ((X0) = (k1_xboole_0)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['55', '56'])).
% 49.25/49.49  thf('58', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((X0) = (k1_xboole_0))
% 49.25/49.49          | ((sk_B) = (k1_xboole_0))
% 49.25/49.49          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('simplify', [status(thm)], ['57'])).
% 49.25/49.49  thf('59', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('60', plain,
% 49.25/49.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('61', plain,
% 49.25/49.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('62', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('63', plain,
% 49.25/49.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 49.25/49.49         ((v4_relat_1 @ X17 @ X18)
% 49.25/49.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 49.25/49.49  thf('64', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 49.25/49.49      inference('sup-', [status(thm)], ['62', '63'])).
% 49.25/49.49  thf('65', plain,
% 49.25/49.49      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup+', [status(thm)], ['61', '64'])).
% 49.25/49.49  thf(t209_relat_1, axiom,
% 49.25/49.49    (![A:$i,B:$i]:
% 49.25/49.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 49.25/49.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 49.25/49.49  thf('66', plain,
% 49.25/49.49      (![X8 : $i, X9 : $i]:
% 49.25/49.49         (((X8) = (k7_relat_1 @ X8 @ X9))
% 49.25/49.49          | ~ (v4_relat_1 @ X8 @ X9)
% 49.25/49.49          | ~ (v1_relat_1 @ X8))),
% 49.25/49.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 49.25/49.49  thf('67', plain,
% 49.25/49.49      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['65', '66'])).
% 49.25/49.49  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('69', plain,
% 49.25/49.49      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['67', '68'])).
% 49.25/49.49  thf('70', plain,
% 49.25/49.49      (![X10 : $i, X11 : $i]:
% 49.25/49.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 49.25/49.49          | ~ (v1_relat_1 @ X10))),
% 49.25/49.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 49.25/49.49  thf(t3_xboole_1, axiom,
% 49.25/49.49    (![A:$i]:
% 49.25/49.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 49.25/49.49  thf('71', plain,
% 49.25/49.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 49.25/49.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 49.25/49.49  thf('72', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (~ (v1_relat_1 @ X0)
% 49.25/49.49          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['70', '71'])).
% 49.25/49.49  thf('73', plain,
% 49.25/49.49      (((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup+', [status(thm)], ['69', '72'])).
% 49.25/49.49  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('75', plain,
% 49.25/49.49      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['73', '74'])).
% 49.25/49.49  thf('76', plain,
% 49.25/49.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 49.25/49.49         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 49.25/49.49          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 49.25/49.49          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 49.25/49.49          | ~ (v1_relat_1 @ X23))),
% 49.25/49.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 49.25/49.49  thf('77', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]:
% 49.25/49.49          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 49.25/49.49           | ~ (v1_relat_1 @ sk_D)
% 49.25/49.49           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 49.25/49.49           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['75', '76'])).
% 49.25/49.49  thf('78', plain,
% 49.25/49.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('79', plain,
% 49.25/49.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('80', plain,
% 49.25/49.49      (((m1_subset_1 @ sk_D @ 
% 49.25/49.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup+', [status(thm)], ['78', '79'])).
% 49.25/49.49  thf('81', plain,
% 49.25/49.49      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['41'])).
% 49.25/49.49  thf('82', plain,
% 49.25/49.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['80', '81'])).
% 49.25/49.49  thf('83', plain,
% 49.25/49.49      (![X2 : $i, X3 : $i]:
% 49.25/49.49         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 49.25/49.49  thf('84', plain,
% 49.25/49.49      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['83'])).
% 49.25/49.49  thf('85', plain,
% 49.25/49.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 49.25/49.49         ((v4_relat_1 @ X17 @ X18)
% 49.25/49.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 49.25/49.49  thf('86', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 49.25/49.49          | (v4_relat_1 @ X1 @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['84', '85'])).
% 49.25/49.49  thf('87', plain,
% 49.25/49.49      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['82', '86'])).
% 49.25/49.49  thf('88', plain,
% 49.25/49.49      (![X8 : $i, X9 : $i]:
% 49.25/49.49         (((X8) = (k7_relat_1 @ X8 @ X9))
% 49.25/49.49          | ~ (v4_relat_1 @ X8 @ X9)
% 49.25/49.49          | ~ (v1_relat_1 @ X8))),
% 49.25/49.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 49.25/49.49  thf('89', plain,
% 49.25/49.49      ((![X0 : $i]:
% 49.25/49.49          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['87', '88'])).
% 49.25/49.49  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('91', plain,
% 49.25/49.49      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['89', '90'])).
% 49.25/49.49  thf('92', plain,
% 49.25/49.49      (![X10 : $i, X11 : $i]:
% 49.25/49.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 49.25/49.49          | ~ (v1_relat_1 @ X10))),
% 49.25/49.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 49.25/49.49  thf('93', plain,
% 49.25/49.49      ((![X0 : $i]:
% 49.25/49.49          ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0) | ~ (v1_relat_1 @ sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup+', [status(thm)], ['91', '92'])).
% 49.25/49.49  thf('94', plain,
% 49.25/49.49      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['73', '74'])).
% 49.25/49.49  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('96', plain,
% 49.25/49.49      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['93', '94', '95'])).
% 49.25/49.49  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('98', plain,
% 49.25/49.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['80', '81'])).
% 49.25/49.49  thf('99', plain,
% 49.25/49.49      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['41'])).
% 49.25/49.49  thf('100', plain,
% 49.25/49.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 49.25/49.49         ((v5_relat_1 @ X17 @ X19)
% 49.25/49.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 49.25/49.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 49.25/49.49  thf('101', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 49.25/49.49          | (v5_relat_1 @ X1 @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['99', '100'])).
% 49.25/49.49  thf('102', plain,
% 49.25/49.49      ((![X0 : $i]: (v5_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['98', '101'])).
% 49.25/49.49  thf('103', plain,
% 49.25/49.49      (![X4 : $i, X5 : $i]:
% 49.25/49.49         (~ (v5_relat_1 @ X4 @ X5)
% 49.25/49.49          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 49.25/49.49          | ~ (v1_relat_1 @ X4))),
% 49.25/49.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 49.25/49.49  thf('104', plain,
% 49.25/49.49      ((![X0 : $i]:
% 49.25/49.49          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['102', '103'])).
% 49.25/49.49  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('106', plain,
% 49.25/49.49      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['104', '105'])).
% 49.25/49.49  thf('107', plain,
% 49.25/49.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 49.25/49.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 49.25/49.49  thf('108', plain,
% 49.25/49.49      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['106', '107'])).
% 49.25/49.49  thf('109', plain,
% 49.25/49.49      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['93', '94', '95'])).
% 49.25/49.49  thf('110', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]:
% 49.25/49.49          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['77', '96', '97', '108', '109'])).
% 49.25/49.49  thf('111', plain,
% 49.25/49.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 49.25/49.49          | ~ (v1_funct_1 @ X38)
% 49.25/49.49          | ((k2_partfun1 @ X39 @ X40 @ X38 @ X41) = (k7_relat_1 @ X38 @ X41)))),
% 49.25/49.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 49.25/49.49  thf('112', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i, X2 : $i]:
% 49.25/49.49          (((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (k7_relat_1 @ sk_D @ X2))
% 49.25/49.49           | ~ (v1_funct_1 @ sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['110', '111'])).
% 49.25/49.49  thf('113', plain,
% 49.25/49.49      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['89', '90'])).
% 49.25/49.49  thf('114', plain, ((v1_funct_1 @ sk_D)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('115', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i, X2 : $i]:
% 49.25/49.49          ((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['112', '113', '114'])).
% 49.25/49.49  thf('116', plain,
% 49.25/49.49      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 49.25/49.49        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 49.25/49.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 49.25/49.49      inference('demod', [status(thm)], ['0', '5'])).
% 49.25/49.49  thf('117', plain,
% 49.25/49.49      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 49.25/49.49         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 49.25/49.49              sk_B)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['115', '116'])).
% 49.25/49.49  thf('118', plain,
% 49.25/49.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('119', plain, ((r1_tarski @ sk_C @ sk_A)),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.25/49.49  thf('120', plain,
% 49.25/49.49      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup+', [status(thm)], ['118', '119'])).
% 49.25/49.49  thf('121', plain,
% 49.25/49.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 49.25/49.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 49.25/49.49  thf('122', plain,
% 49.25/49.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['120', '121'])).
% 49.25/49.49  thf('123', plain,
% 49.25/49.49      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['41'])).
% 49.25/49.49  thf('124', plain,
% 49.25/49.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['80', '81'])).
% 49.25/49.49  thf('125', plain,
% 49.25/49.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('126', plain,
% 49.25/49.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['120', '121'])).
% 49.25/49.49  thf('127', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i, X2 : $i]:
% 49.25/49.49          ((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['112', '113', '114'])).
% 49.25/49.49  thf('128', plain,
% 49.25/49.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['120', '121'])).
% 49.25/49.49  thf('129', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]:
% 49.25/49.49          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['77', '96', '97', '108', '109'])).
% 49.25/49.49  thf('130', plain,
% 49.25/49.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 49.25/49.49         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 49.25/49.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 49.25/49.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 49.25/49.49  thf('131', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]:
% 49.25/49.49          ((k1_relset_1 @ X1 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['129', '130'])).
% 49.25/49.49  thf('132', plain,
% 49.25/49.49      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['73', '74'])).
% 49.25/49.49  thf('133', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]: ((k1_relset_1 @ X1 @ X0 @ sk_D) = (k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['131', '132'])).
% 49.25/49.49  thf('134', plain,
% 49.25/49.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 49.25/49.49         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 49.25/49.49          | (v1_funct_2 @ X30 @ X28 @ X29)
% 49.25/49.49          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 49.25/49.49  thf('135', plain,
% 49.25/49.49      ((![X0 : $i, X1 : $i]:
% 49.25/49.49          (((X1) != (k1_xboole_0))
% 49.25/49.49           | ~ (zip_tseitin_1 @ sk_D @ X0 @ X1)
% 49.25/49.49           | (v1_funct_2 @ sk_D @ X1 @ X0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['133', '134'])).
% 49.25/49.49  thf('136', plain,
% 49.25/49.49      ((![X0 : $i]:
% 49.25/49.49          ((v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)
% 49.25/49.49           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('simplify', [status(thm)], ['135'])).
% 49.25/49.49  thf('137', plain,
% 49.25/49.49      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['80', '81'])).
% 49.25/49.49  thf('138', plain,
% 49.25/49.49      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 49.25/49.49      inference('simplify', [status(thm)], ['41'])).
% 49.25/49.49  thf('139', plain,
% 49.25/49.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 49.25/49.49         (~ (zip_tseitin_0 @ X31 @ X32)
% 49.25/49.49          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 49.25/49.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 49.25/49.49  thf('140', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 49.25/49.49          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 49.25/49.49          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['138', '139'])).
% 49.25/49.49  thf('141', plain,
% 49.25/49.49      (![X26 : $i, X27 : $i]:
% 49.25/49.49         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 49.25/49.49  thf('142', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 49.25/49.49      inference('simplify', [status(thm)], ['141'])).
% 49.25/49.49  thf('143', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]:
% 49.25/49.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 49.25/49.49          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 49.25/49.49      inference('demod', [status(thm)], ['140', '142'])).
% 49.25/49.49  thf('144', plain,
% 49.25/49.49      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('sup-', [status(thm)], ['137', '143'])).
% 49.25/49.49  thf('145', plain,
% 49.25/49.49      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 49.25/49.49         <= ((((sk_A) = (k1_xboole_0))))),
% 49.25/49.49      inference('demod', [status(thm)], ['136', '144'])).
% 49.25/49.49  thf('146', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 49.25/49.49      inference('demod', [status(thm)],
% 49.25/49.49                ['117', '122', '123', '124', '125', '126', '127', '128', '145'])).
% 49.25/49.49  thf('147', plain,
% 49.25/49.49      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 49.25/49.49      inference('split', [status(esa)], ['59'])).
% 49.25/49.49  thf('148', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 49.25/49.49      inference('sat_resolution*', [status(thm)], ['146', '147'])).
% 49.25/49.49  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 49.25/49.49      inference('simpl_trail', [status(thm)], ['60', '148'])).
% 49.25/49.49  thf('150', plain,
% 49.25/49.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('simplify_reflect-', [status(thm)], ['58', '149'])).
% 49.25/49.49  thf('151', plain,
% 49.25/49.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('simplify_reflect-', [status(thm)], ['58', '149'])).
% 49.25/49.49  thf('152', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]:
% 49.25/49.49         (((X1) = (X0))
% 49.25/49.49          | ((sk_A) = (k1_relat_1 @ sk_D))
% 49.25/49.49          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 49.25/49.49      inference('sup+', [status(thm)], ['150', '151'])).
% 49.25/49.49  thf('153', plain,
% 49.25/49.49      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 49.25/49.49      inference('simplify', [status(thm)], ['152'])).
% 49.25/49.49  thf('154', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 49.25/49.49      inference('condensation', [status(thm)], ['153'])).
% 49.25/49.49  thf(t91_relat_1, axiom,
% 49.25/49.49    (![A:$i,B:$i]:
% 49.25/49.49     ( ( v1_relat_1 @ B ) =>
% 49.25/49.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 49.25/49.49         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 49.25/49.49  thf('155', plain,
% 49.25/49.49      (![X12 : $i, X13 : $i]:
% 49.25/49.49         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 49.25/49.49          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 49.25/49.49          | ~ (v1_relat_1 @ X13))),
% 49.25/49.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 49.25/49.49  thf('156', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (~ (r1_tarski @ X0 @ sk_A)
% 49.25/49.49          | ~ (v1_relat_1 @ sk_D)
% 49.25/49.49          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['154', '155'])).
% 49.25/49.49  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 49.25/49.49      inference('sup-', [status(thm)], ['34', '35'])).
% 49.25/49.49  thf('158', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (~ (r1_tarski @ X0 @ sk_A)
% 49.25/49.49          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 49.25/49.49      inference('demod', [status(thm)], ['156', '157'])).
% 49.25/49.49  thf('159', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 49.25/49.49      inference('sup-', [status(thm)], ['39', '158'])).
% 49.25/49.49  thf('160', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['32', '33', '36'])).
% 49.25/49.49  thf('161', plain,
% 49.25/49.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 49.25/49.49         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 49.25/49.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 49.25/49.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 49.25/49.49  thf('162', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 49.25/49.49           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 49.25/49.49      inference('sup-', [status(thm)], ['160', '161'])).
% 49.25/49.49  thf('163', plain,
% 49.25/49.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 49.25/49.49         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 49.25/49.49          | (v1_funct_2 @ X30 @ X28 @ X29)
% 49.25/49.49          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 49.25/49.49  thf('164', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 49.25/49.49          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 49.25/49.49          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 49.25/49.49      inference('sup-', [status(thm)], ['162', '163'])).
% 49.25/49.49  thf('165', plain,
% 49.25/49.49      (![X26 : $i, X27 : $i]:
% 49.25/49.49         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 49.25/49.49  thf('166', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 49.25/49.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 49.25/49.49      inference('demod', [status(thm)], ['32', '33', '36'])).
% 49.25/49.49  thf('167', plain,
% 49.25/49.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 49.25/49.49         (~ (zip_tseitin_0 @ X31 @ X32)
% 49.25/49.49          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 49.25/49.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 49.25/49.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 49.25/49.49  thf('168', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 49.25/49.49          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['166', '167'])).
% 49.25/49.49  thf('169', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((sk_B) = (k1_xboole_0))
% 49.25/49.49          | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0))),
% 49.25/49.49      inference('sup-', [status(thm)], ['165', '168'])).
% 49.25/49.49  thf('170', plain, (((sk_B) != (k1_xboole_0))),
% 49.25/49.49      inference('simpl_trail', [status(thm)], ['60', '148'])).
% 49.25/49.49  thf('171', plain,
% 49.25/49.49      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 49.25/49.49      inference('simplify_reflect-', [status(thm)], ['169', '170'])).
% 49.25/49.49  thf('172', plain,
% 49.25/49.49      (![X0 : $i]:
% 49.25/49.49         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 49.25/49.49          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 49.25/49.49      inference('demod', [status(thm)], ['164', '171'])).
% 49.25/49.49  thf('173', plain,
% 49.25/49.49      ((((sk_C) != (sk_C))
% 49.25/49.49        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 49.25/49.49      inference('sup-', [status(thm)], ['159', '172'])).
% 49.25/49.49  thf('174', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 49.25/49.49      inference('simplify', [status(thm)], ['173'])).
% 49.25/49.49  thf('175', plain, ($false), inference('demod', [status(thm)], ['38', '174'])).
% 49.25/49.49  
% 49.25/49.49  % SZS output end Refutation
% 49.25/49.49  
% 49.25/49.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
