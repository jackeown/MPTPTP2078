%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tG2yGehReQ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:36 EST 2020

% Result     : Theorem 6.46s
% Output     : Refutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  223 (1667 expanded)
%              Number of leaves         :   40 ( 485 expanded)
%              Depth                    :   29
%              Number of atoms          : 1799 (27507 expanded)
%              Number of equality atoms :  167 (1824 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 )
        = ( k7_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','6','7'])).

thf('72',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('74',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('85',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('94',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('96',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('102',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('104',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','102','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('111',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ X1 )
        | ( v1_funct_2 @ sk_D @ X1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('118',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('119',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('122',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['120','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','124'])).

thf('126',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['72','77','78','79','80','81','82','125','126','127','128'])).

thf('130',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('131',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','132'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['136'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('138',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['35','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('144',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('149',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X2 )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X1 ) )
      | ( ( k7_relat_1 @ sk_D @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('160',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X2 )
      | ( ( k7_relat_1 @ sk_D @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ sk_B @ X2 ) ) ),
    inference('sup+',[status(thm)],['151','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','131'])).

thf('176',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['150','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','177'])).

thf('179',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['142','178'])).

thf('180',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    $false ),
    inference(demod,[status(thm)],['34','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tG2yGehReQ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.46/6.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.46/6.69  % Solved by: fo/fo7.sh
% 6.46/6.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.46/6.69  % done 2913 iterations in 6.240s
% 6.46/6.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.46/6.69  % SZS output start Refutation
% 6.46/6.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.46/6.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.46/6.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.46/6.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.46/6.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.46/6.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.46/6.69  thf(sk_C_type, type, sk_C: $i).
% 6.46/6.69  thf(sk_D_type, type, sk_D: $i).
% 6.46/6.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.46/6.69  thf(sk_A_type, type, sk_A: $i).
% 6.46/6.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.46/6.69  thf(sk_B_type, type, sk_B: $i).
% 6.46/6.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.46/6.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.46/6.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.46/6.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.46/6.69  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 6.46/6.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.46/6.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.46/6.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.46/6.69  thf(t38_funct_2, conjecture,
% 6.46/6.69    (![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.46/6.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.46/6.69       ( ( r1_tarski @ C @ A ) =>
% 6.46/6.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 6.46/6.69           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 6.46/6.69             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 6.46/6.69             ( m1_subset_1 @
% 6.46/6.69               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 6.46/6.69               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 6.46/6.69  thf(zf_stmt_0, negated_conjecture,
% 6.46/6.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.46/6.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.46/6.69          ( ( r1_tarski @ C @ A ) =>
% 6.46/6.69            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 6.46/6.69              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 6.46/6.69                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 6.46/6.69                ( m1_subset_1 @
% 6.46/6.69                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 6.46/6.69                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 6.46/6.69    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 6.46/6.69  thf('0', plain,
% 6.46/6.69      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 6.46/6.69        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 6.46/6.69             sk_B)
% 6.46/6.69        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 6.46/6.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('1', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(redefinition_k2_partfun1, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.69     ( ( ( v1_funct_1 @ C ) & 
% 6.46/6.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.46/6.69       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 6.46/6.69  thf('2', plain,
% 6.46/6.69      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.46/6.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 6.46/6.69          | ~ (v1_funct_1 @ X39)
% 6.46/6.69          | ((k2_partfun1 @ X40 @ X41 @ X39 @ X42) = (k7_relat_1 @ X39 @ X42)))),
% 6.46/6.69      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 6.46/6.69  thf('3', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 6.46/6.69          | ~ (v1_funct_1 @ sk_D))),
% 6.46/6.69      inference('sup-', [status(thm)], ['1', '2'])).
% 6.46/6.69  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('5', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['3', '4'])).
% 6.46/6.69  thf('6', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['3', '4'])).
% 6.46/6.69  thf('7', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['3', '4'])).
% 6.46/6.69  thf('8', plain,
% 6.46/6.69      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))
% 6.46/6.69        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 6.46/6.69        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 6.46/6.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 6.46/6.69      inference('demod', [status(thm)], ['0', '5', '6', '7'])).
% 6.46/6.69  thf('9', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(dt_k2_partfun1, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.69     ( ( ( v1_funct_1 @ C ) & 
% 6.46/6.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.46/6.69       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 6.46/6.69         ( m1_subset_1 @
% 6.46/6.69           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 6.46/6.69           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 6.46/6.69  thf('10', plain,
% 6.46/6.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.46/6.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.46/6.69          | ~ (v1_funct_1 @ X35)
% 6.46/6.69          | (v1_funct_1 @ (k2_partfun1 @ X36 @ X37 @ X35 @ X38)))),
% 6.46/6.69      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 6.46/6.69  thf('11', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 6.46/6.69          | ~ (v1_funct_1 @ sk_D))),
% 6.46/6.69      inference('sup-', [status(thm)], ['9', '10'])).
% 6.46/6.69  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('13', plain,
% 6.46/6.69      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['11', '12'])).
% 6.46/6.69  thf('14', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['3', '4'])).
% 6.46/6.69  thf('15', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['13', '14'])).
% 6.46/6.69  thf('16', plain,
% 6.46/6.69      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 6.46/6.69        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 6.46/6.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 6.46/6.69      inference('demod', [status(thm)], ['8', '15'])).
% 6.46/6.69  thf(t87_relat_1, axiom,
% 6.46/6.69    (![A:$i,B:$i]:
% 6.46/6.69     ( ( v1_relat_1 @ B ) =>
% 6.46/6.69       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 6.46/6.69  thf('17', plain,
% 6.46/6.69      (![X10 : $i, X11 : $i]:
% 6.46/6.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 6.46/6.69          | ~ (v1_relat_1 @ X10))),
% 6.46/6.69      inference('cnf', [status(esa)], [t87_relat_1])).
% 6.46/6.69  thf('18', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('19', plain,
% 6.46/6.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.46/6.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.46/6.69          | ~ (v1_funct_1 @ X35)
% 6.46/6.69          | (m1_subset_1 @ (k2_partfun1 @ X36 @ X37 @ X35 @ X38) @ 
% 6.46/6.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 6.46/6.69      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 6.46/6.69  thf('20', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 6.46/6.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.46/6.69          | ~ (v1_funct_1 @ sk_D))),
% 6.46/6.69      inference('sup-', [status(thm)], ['18', '19'])).
% 6.46/6.69  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('22', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 6.46/6.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('demod', [status(thm)], ['20', '21'])).
% 6.46/6.69  thf('23', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.69      inference('demod', [status(thm)], ['3', '4'])).
% 6.46/6.69  thf('24', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('demod', [status(thm)], ['22', '23'])).
% 6.46/6.69  thf(t13_relset_1, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.69     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 6.46/6.69       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 6.46/6.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 6.46/6.69  thf('25', plain,
% 6.46/6.69      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.46/6.69         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 6.46/6.69          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 6.46/6.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 6.46/6.69      inference('cnf', [status(esa)], [t13_relset_1])).
% 6.46/6.69  thf('26', plain,
% 6.46/6.69      (![X0 : $i, X1 : $i]:
% 6.46/6.69         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.46/6.69          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 6.46/6.69      inference('sup-', [status(thm)], ['24', '25'])).
% 6.46/6.69  thf('27', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (~ (v1_relat_1 @ sk_D)
% 6.46/6.69          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 6.46/6.69      inference('sup-', [status(thm)], ['17', '26'])).
% 6.46/6.69  thf('28', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(cc2_relat_1, axiom,
% 6.46/6.69    (![A:$i]:
% 6.46/6.69     ( ( v1_relat_1 @ A ) =>
% 6.46/6.69       ( ![B:$i]:
% 6.46/6.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.46/6.69  thf('29', plain,
% 6.46/6.69      (![X4 : $i, X5 : $i]:
% 6.46/6.69         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 6.46/6.69          | (v1_relat_1 @ X4)
% 6.46/6.69          | ~ (v1_relat_1 @ X5))),
% 6.46/6.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.46/6.69  thf('30', plain,
% 6.46/6.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 6.46/6.69      inference('sup-', [status(thm)], ['28', '29'])).
% 6.46/6.69  thf(fc6_relat_1, axiom,
% 6.46/6.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.46/6.69  thf('31', plain,
% 6.46/6.69      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 6.46/6.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.46/6.69  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.69      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.69  thf('33', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 6.46/6.69      inference('demod', [status(thm)], ['27', '32'])).
% 6.46/6.69  thf('34', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 6.46/6.69      inference('demod', [status(thm)], ['16', '33'])).
% 6.46/6.69  thf('35', plain, ((r1_tarski @ sk_C @ sk_A)),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(d1_funct_2, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i]:
% 6.46/6.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.46/6.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.46/6.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.46/6.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.46/6.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.46/6.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.46/6.69  thf(zf_stmt_1, axiom,
% 6.46/6.69    (![B:$i,A:$i]:
% 6.46/6.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.46/6.69       ( zip_tseitin_0 @ B @ A ) ))).
% 6.46/6.69  thf('36', plain,
% 6.46/6.69      (![X27 : $i, X28 : $i]:
% 6.46/6.69         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.46/6.69  thf(t113_zfmisc_1, axiom,
% 6.46/6.69    (![A:$i,B:$i]:
% 6.46/6.69     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.46/6.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.46/6.69  thf('37', plain,
% 6.46/6.69      (![X2 : $i, X3 : $i]:
% 6.46/6.69         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 6.46/6.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.46/6.69  thf('38', plain,
% 6.46/6.69      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 6.46/6.69      inference('simplify', [status(thm)], ['37'])).
% 6.46/6.69  thf('39', plain,
% 6.46/6.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.69         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.46/6.69      inference('sup+', [status(thm)], ['36', '38'])).
% 6.46/6.69  thf('40', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.46/6.69  thf(zf_stmt_3, axiom,
% 6.46/6.69    (![C:$i,B:$i,A:$i]:
% 6.46/6.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.46/6.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.46/6.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.46/6.69  thf(zf_stmt_5, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i]:
% 6.46/6.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.46/6.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.46/6.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.46/6.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.46/6.69  thf('41', plain,
% 6.46/6.69      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.46/6.69         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.46/6.69          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.46/6.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.46/6.69  thf('42', plain,
% 6.46/6.69      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.46/6.69      inference('sup-', [status(thm)], ['40', '41'])).
% 6.46/6.69  thf('43', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 6.46/6.69          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 6.46/6.69      inference('sup-', [status(thm)], ['39', '42'])).
% 6.46/6.69  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('45', plain,
% 6.46/6.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.46/6.69         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 6.46/6.69          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 6.46/6.69          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.46/6.69  thf('46', plain,
% 6.46/6.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 6.46/6.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 6.46/6.69      inference('sup-', [status(thm)], ['44', '45'])).
% 6.46/6.69  thf('47', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf(redefinition_k1_relset_1, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i]:
% 6.46/6.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.46/6.69  thf('48', plain,
% 6.46/6.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.46/6.69         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.46/6.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.46/6.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.46/6.69  thf('49', plain,
% 6.46/6.69      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.46/6.69      inference('sup-', [status(thm)], ['47', '48'])).
% 6.46/6.69  thf('50', plain,
% 6.46/6.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.69      inference('demod', [status(thm)], ['46', '49'])).
% 6.46/6.69  thf('51', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 6.46/6.69          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.69      inference('sup-', [status(thm)], ['43', '50'])).
% 6.46/6.69  thf('52', plain,
% 6.46/6.69      (![X1 : $i, X2 : $i]:
% 6.46/6.69         (((X1) = (k1_xboole_0))
% 6.46/6.69          | ((X2) = (k1_xboole_0))
% 6.46/6.69          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 6.46/6.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.46/6.69  thf('53', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (((k1_xboole_0) != (k1_xboole_0))
% 6.46/6.69          | ((sk_A) = (k1_relat_1 @ sk_D))
% 6.46/6.69          | ((X0) = (k1_xboole_0))
% 6.46/6.69          | ((sk_B) = (k1_xboole_0)))),
% 6.46/6.69      inference('sup-', [status(thm)], ['51', '52'])).
% 6.46/6.69  thf('54', plain,
% 6.46/6.69      (![X0 : $i]:
% 6.46/6.69         (((sk_B) = (k1_xboole_0))
% 6.46/6.69          | ((X0) = (k1_xboole_0))
% 6.46/6.69          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.69      inference('simplify', [status(thm)], ['53'])).
% 6.46/6.69  thf('55', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('56', plain,
% 6.46/6.69      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 6.46/6.69      inference('split', [status(esa)], ['55'])).
% 6.46/6.69  thf('57', plain,
% 6.46/6.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.69      inference('split', [status(esa)], ['55'])).
% 6.46/6.69  thf('58', plain,
% 6.46/6.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.69  thf('59', plain,
% 6.46/6.69      (((m1_subset_1 @ sk_D @ 
% 6.46/6.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 6.46/6.69         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.69      inference('sup+', [status(thm)], ['57', '58'])).
% 6.46/6.69  thf('60', plain,
% 6.46/6.69      (![X2 : $i, X3 : $i]:
% 6.46/6.69         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 6.46/6.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.46/6.69  thf('61', plain,
% 6.46/6.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 6.46/6.69      inference('simplify', [status(thm)], ['60'])).
% 6.46/6.69  thf('62', plain,
% 6.46/6.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 6.46/6.69         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.69      inference('demod', [status(thm)], ['59', '61'])).
% 6.46/6.69  thf('63', plain,
% 6.46/6.69      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 6.46/6.69      inference('simplify', [status(thm)], ['37'])).
% 6.46/6.69  thf(cc2_relset_1, axiom,
% 6.46/6.69    (![A:$i,B:$i,C:$i]:
% 6.46/6.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.46/6.69  thf('64', plain,
% 6.46/6.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.46/6.69         ((v4_relat_1 @ X17 @ X18)
% 6.46/6.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.46/6.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.46/6.70  thf('65', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (v4_relat_1 @ X1 @ X0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['63', '64'])).
% 6.46/6.70  thf('66', plain,
% 6.46/6.70      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['62', '65'])).
% 6.46/6.70  thf(t209_relat_1, axiom,
% 6.46/6.70    (![A:$i,B:$i]:
% 6.46/6.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.46/6.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 6.46/6.70  thf('67', plain,
% 6.46/6.70      (![X8 : $i, X9 : $i]:
% 6.46/6.70         (((X8) = (k7_relat_1 @ X8 @ X9))
% 6.46/6.70          | ~ (v4_relat_1 @ X8 @ X9)
% 6.46/6.70          | ~ (v1_relat_1 @ X8))),
% 6.46/6.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.46/6.70  thf('68', plain,
% 6.46/6.70      ((![X0 : $i]:
% 6.46/6.70          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['66', '67'])).
% 6.46/6.70  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('70', plain,
% 6.46/6.70      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['68', '69'])).
% 6.46/6.70  thf('71', plain,
% 6.46/6.70      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))
% 6.46/6.70        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 6.46/6.70        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 6.46/6.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 6.46/6.70      inference('demod', [status(thm)], ['0', '5', '6', '7'])).
% 6.46/6.70  thf('72', plain,
% 6.46/6.70      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 6.46/6.70         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 6.46/6.70         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['70', '71'])).
% 6.46/6.70  thf('73', plain,
% 6.46/6.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('split', [status(esa)], ['55'])).
% 6.46/6.70  thf('74', plain, ((r1_tarski @ sk_C @ sk_A)),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.70  thf('75', plain,
% 6.46/6.70      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup+', [status(thm)], ['73', '74'])).
% 6.46/6.70  thf(t3_xboole_1, axiom,
% 6.46/6.70    (![A:$i]:
% 6.46/6.70     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.46/6.70  thf('76', plain,
% 6.46/6.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.46/6.70      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.46/6.70  thf('77', plain,
% 6.46/6.70      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['75', '76'])).
% 6.46/6.70  thf('78', plain,
% 6.46/6.70      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 6.46/6.70      inference('simplify', [status(thm)], ['60'])).
% 6.46/6.70  thf('79', plain,
% 6.46/6.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['59', '61'])).
% 6.46/6.70  thf('80', plain,
% 6.46/6.70      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['75', '76'])).
% 6.46/6.70  thf('81', plain,
% 6.46/6.70      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['68', '69'])).
% 6.46/6.70  thf('82', plain,
% 6.46/6.70      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['75', '76'])).
% 6.46/6.70  thf('83', plain,
% 6.46/6.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['59', '61'])).
% 6.46/6.70  thf('84', plain,
% 6.46/6.70      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 6.46/6.70      inference('simplify', [status(thm)], ['60'])).
% 6.46/6.70  thf('85', plain,
% 6.46/6.70      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.46/6.70         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 6.46/6.70          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 6.46/6.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 6.46/6.70      inference('cnf', [status(esa)], [t13_relset_1])).
% 6.46/6.70  thf('86', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.46/6.70          | ~ (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 6.46/6.70      inference('sup-', [status(thm)], ['84', '85'])).
% 6.46/6.70  thf('87', plain,
% 6.46/6.70      ((![X0 : $i, X1 : $i]:
% 6.46/6.70          (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 6.46/6.70           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['83', '86'])).
% 6.46/6.70  thf('88', plain,
% 6.46/6.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('split', [status(esa)], ['55'])).
% 6.46/6.70  thf('89', plain,
% 6.46/6.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.70  thf('90', plain,
% 6.46/6.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.46/6.70         ((v4_relat_1 @ X17 @ X18)
% 6.46/6.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.46/6.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.46/6.70  thf('91', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 6.46/6.70      inference('sup-', [status(thm)], ['89', '90'])).
% 6.46/6.70  thf('92', plain,
% 6.46/6.70      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup+', [status(thm)], ['88', '91'])).
% 6.46/6.70  thf('93', plain,
% 6.46/6.70      (![X8 : $i, X9 : $i]:
% 6.46/6.70         (((X8) = (k7_relat_1 @ X8 @ X9))
% 6.46/6.70          | ~ (v4_relat_1 @ X8 @ X9)
% 6.46/6.70          | ~ (v1_relat_1 @ X8))),
% 6.46/6.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.46/6.70  thf('94', plain,
% 6.46/6.70      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['92', '93'])).
% 6.46/6.70  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('96', plain,
% 6.46/6.70      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['94', '95'])).
% 6.46/6.70  thf('97', plain,
% 6.46/6.70      (![X10 : $i, X11 : $i]:
% 6.46/6.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 6.46/6.70          | ~ (v1_relat_1 @ X10))),
% 6.46/6.70      inference('cnf', [status(esa)], [t87_relat_1])).
% 6.46/6.70  thf('98', plain,
% 6.46/6.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.46/6.70      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.46/6.70  thf('99', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (~ (v1_relat_1 @ X0)
% 6.46/6.70          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['97', '98'])).
% 6.46/6.70  thf('100', plain,
% 6.46/6.70      (((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup+', [status(thm)], ['96', '99'])).
% 6.46/6.70  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('102', plain,
% 6.46/6.70      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['100', '101'])).
% 6.46/6.70  thf('103', plain,
% 6.46/6.70      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['68', '69'])).
% 6.46/6.70  thf('104', plain,
% 6.46/6.70      (![X10 : $i, X11 : $i]:
% 6.46/6.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 6.46/6.70          | ~ (v1_relat_1 @ X10))),
% 6.46/6.70      inference('cnf', [status(esa)], [t87_relat_1])).
% 6.46/6.70  thf('105', plain,
% 6.46/6.70      ((![X0 : $i]:
% 6.46/6.70          ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0) | ~ (v1_relat_1 @ sk_D)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup+', [status(thm)], ['103', '104'])).
% 6.46/6.70  thf('106', plain,
% 6.46/6.70      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['100', '101'])).
% 6.46/6.70  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('108', plain,
% 6.46/6.70      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['105', '106', '107'])).
% 6.46/6.70  thf('109', plain,
% 6.46/6.70      ((![X0 : $i, X1 : $i]:
% 6.46/6.70          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['87', '102', '108'])).
% 6.46/6.70  thf('110', plain,
% 6.46/6.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.46/6.70         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.46/6.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.46/6.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.46/6.70  thf('111', plain,
% 6.46/6.70      ((![X0 : $i, X1 : $i]:
% 6.46/6.70          ((k1_relset_1 @ X1 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['109', '110'])).
% 6.46/6.70  thf('112', plain,
% 6.46/6.70      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['100', '101'])).
% 6.46/6.70  thf('113', plain,
% 6.46/6.70      ((![X0 : $i, X1 : $i]: ((k1_relset_1 @ X1 @ X0 @ sk_D) = (k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['111', '112'])).
% 6.46/6.70  thf('114', plain,
% 6.46/6.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.46/6.70         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 6.46/6.70          | (v1_funct_2 @ X31 @ X29 @ X30)
% 6.46/6.70          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.46/6.70  thf('115', plain,
% 6.46/6.70      ((![X0 : $i, X1 : $i]:
% 6.46/6.70          (((X1) != (k1_xboole_0))
% 6.46/6.70           | ~ (zip_tseitin_1 @ sk_D @ X0 @ X1)
% 6.46/6.70           | (v1_funct_2 @ sk_D @ X1 @ X0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['113', '114'])).
% 6.46/6.70  thf('116', plain,
% 6.46/6.70      ((![X0 : $i]:
% 6.46/6.70          ((v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)
% 6.46/6.70           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('simplify', [status(thm)], ['115'])).
% 6.46/6.70  thf('117', plain,
% 6.46/6.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['59', '61'])).
% 6.46/6.70  thf('118', plain,
% 6.46/6.70      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 6.46/6.70      inference('simplify', [status(thm)], ['60'])).
% 6.46/6.70  thf('119', plain,
% 6.46/6.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.46/6.70         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.46/6.70          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.46/6.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.46/6.70  thf('120', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 6.46/6.70          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['118', '119'])).
% 6.46/6.70  thf('121', plain,
% 6.46/6.70      (![X27 : $i, X28 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.46/6.70  thf('122', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 6.46/6.70      inference('simplify', [status(thm)], ['121'])).
% 6.46/6.70  thf('123', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 6.46/6.70      inference('demod', [status(thm)], ['120', '122'])).
% 6.46/6.70  thf('124', plain,
% 6.46/6.70      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['117', '123'])).
% 6.46/6.70  thf('125', plain,
% 6.46/6.70      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['116', '124'])).
% 6.46/6.70  thf('126', plain,
% 6.46/6.70      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('sup-', [status(thm)], ['75', '76'])).
% 6.46/6.70  thf('127', plain,
% 6.46/6.70      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70         <= ((((sk_A) = (k1_xboole_0))))),
% 6.46/6.70      inference('demod', [status(thm)], ['68', '69'])).
% 6.46/6.70  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.70  thf('129', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 6.46/6.70      inference('demod', [status(thm)],
% 6.46/6.70                ['72', '77', '78', '79', '80', '81', '82', '125', '126', 
% 6.46/6.70                 '127', '128'])).
% 6.46/6.70  thf('130', plain,
% 6.46/6.70      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 6.46/6.70      inference('split', [status(esa)], ['55'])).
% 6.46/6.70  thf('131', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 6.46/6.70      inference('sat_resolution*', [status(thm)], ['129', '130'])).
% 6.46/6.70  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 6.46/6.70      inference('simpl_trail', [status(thm)], ['56', '131'])).
% 6.46/6.70  thf('133', plain,
% 6.46/6.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.70      inference('simplify_reflect-', [status(thm)], ['54', '132'])).
% 6.46/6.70  thf('134', plain,
% 6.46/6.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.70      inference('simplify_reflect-', [status(thm)], ['54', '132'])).
% 6.46/6.70  thf('135', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (((X1) = (X0))
% 6.46/6.70          | ((sk_A) = (k1_relat_1 @ sk_D))
% 6.46/6.70          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.46/6.70      inference('sup+', [status(thm)], ['133', '134'])).
% 6.46/6.70  thf('136', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 6.46/6.70      inference('simplify', [status(thm)], ['135'])).
% 6.46/6.70  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.46/6.70      inference('condensation', [status(thm)], ['136'])).
% 6.46/6.70  thf(t91_relat_1, axiom,
% 6.46/6.70    (![A:$i,B:$i]:
% 6.46/6.70     ( ( v1_relat_1 @ B ) =>
% 6.46/6.70       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 6.46/6.70         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 6.46/6.70  thf('138', plain,
% 6.46/6.70      (![X12 : $i, X13 : $i]:
% 6.46/6.70         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 6.46/6.70          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 6.46/6.70          | ~ (v1_relat_1 @ X13))),
% 6.46/6.70      inference('cnf', [status(esa)], [t91_relat_1])).
% 6.46/6.70  thf('139', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (~ (r1_tarski @ X0 @ sk_A)
% 6.46/6.70          | ~ (v1_relat_1 @ sk_D)
% 6.46/6.70          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['137', '138'])).
% 6.46/6.70  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('141', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (~ (r1_tarski @ X0 @ sk_A)
% 6.46/6.70          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 6.46/6.70      inference('demod', [status(thm)], ['139', '140'])).
% 6.46/6.70  thf('142', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 6.46/6.70      inference('sup-', [status(thm)], ['35', '141'])).
% 6.46/6.70  thf('143', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 6.46/6.70      inference('demod', [status(thm)], ['27', '32'])).
% 6.46/6.70  thf('144', plain,
% 6.46/6.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.46/6.70         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.46/6.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.46/6.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.46/6.70  thf('145', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 6.46/6.70           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['143', '144'])).
% 6.46/6.70  thf('146', plain,
% 6.46/6.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.46/6.70         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 6.46/6.70          | (v1_funct_2 @ X31 @ X29 @ X30)
% 6.46/6.70          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.46/6.70  thf('147', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 6.46/6.70          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 6.46/6.70      inference('sup-', [status(thm)], ['145', '146'])).
% 6.46/6.70  thf('148', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 6.46/6.70      inference('demod', [status(thm)], ['27', '32'])).
% 6.46/6.70  thf('149', plain,
% 6.46/6.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.46/6.70         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.46/6.70          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.46/6.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.46/6.70  thf('150', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 6.46/6.70          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['148', '149'])).
% 6.46/6.70  thf('151', plain,
% 6.46/6.70      (![X27 : $i, X28 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 6.46/6.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.46/6.70  thf('152', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.46/6.70      inference('sup+', [status(thm)], ['36', '38'])).
% 6.46/6.70  thf('153', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.70      inference('demod', [status(thm)], ['22', '23'])).
% 6.46/6.70  thf('154', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (zip_tseitin_0 @ sk_B @ X1))),
% 6.46/6.70      inference('sup+', [status(thm)], ['152', '153'])).
% 6.46/6.70  thf('155', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.46/6.70          | (v4_relat_1 @ X1 @ X0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['63', '64'])).
% 6.46/6.70  thf('156', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ sk_B @ X2)
% 6.46/6.70          | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 6.46/6.70      inference('sup-', [status(thm)], ['154', '155'])).
% 6.46/6.70  thf('157', plain,
% 6.46/6.70      (![X8 : $i, X9 : $i]:
% 6.46/6.70         (((X8) = (k7_relat_1 @ X8 @ X9))
% 6.46/6.70          | ~ (v4_relat_1 @ X8 @ X9)
% 6.46/6.70          | ~ (v1_relat_1 @ X8))),
% 6.46/6.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.46/6.70  thf('158', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ sk_B @ X2)
% 6.46/6.70          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X1))
% 6.46/6.70          | ((k7_relat_1 @ sk_D @ X1)
% 6.46/6.70              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X1) @ X0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['156', '157'])).
% 6.46/6.70  thf('159', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 6.46/6.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.46/6.70      inference('demod', [status(thm)], ['22', '23'])).
% 6.46/6.70  thf(cc1_relset_1, axiom,
% 6.46/6.70    (![A:$i,B:$i,C:$i]:
% 6.46/6.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.70       ( v1_relat_1 @ C ) ))).
% 6.46/6.70  thf('160', plain,
% 6.46/6.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.46/6.70         ((v1_relat_1 @ X14)
% 6.46/6.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.46/6.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.46/6.70  thf('161', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['159', '160'])).
% 6.46/6.70  thf('162', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ sk_B @ X2)
% 6.46/6.70          | ((k7_relat_1 @ sk_D @ X1)
% 6.46/6.70              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X1) @ X0)))),
% 6.46/6.70      inference('demod', [status(thm)], ['158', '161'])).
% 6.46/6.70  thf('163', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (~ (v1_relat_1 @ X0)
% 6.46/6.70          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['97', '98'])).
% 6.46/6.70  thf('164', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k1_xboole_0))
% 6.46/6.70          | (zip_tseitin_0 @ sk_B @ X1)
% 6.46/6.70          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 6.46/6.70      inference('sup+', [status(thm)], ['162', '163'])).
% 6.46/6.70  thf('165', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 6.46/6.70      inference('sup-', [status(thm)], ['159', '160'])).
% 6.46/6.70  thf('166', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (k1_xboole_0))
% 6.46/6.70          | (zip_tseitin_0 @ sk_B @ X1))),
% 6.46/6.70      inference('demod', [status(thm)], ['164', '165'])).
% 6.46/6.70  thf('167', plain,
% 6.46/6.70      (![X10 : $i, X11 : $i]:
% 6.46/6.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 6.46/6.70          | ~ (v1_relat_1 @ X10))),
% 6.46/6.70      inference('cnf', [status(esa)], [t87_relat_1])).
% 6.46/6.70  thf('168', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         ((r1_tarski @ k1_xboole_0 @ X0)
% 6.46/6.70          | (zip_tseitin_0 @ sk_B @ X1)
% 6.46/6.70          | ~ (v1_relat_1 @ sk_D))),
% 6.46/6.70      inference('sup+', [status(thm)], ['166', '167'])).
% 6.46/6.70  thf('169', plain, ((v1_relat_1 @ sk_D)),
% 6.46/6.70      inference('demod', [status(thm)], ['30', '31'])).
% 6.46/6.70  thf('170', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         ((r1_tarski @ k1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 6.46/6.70      inference('demod', [status(thm)], ['168', '169'])).
% 6.46/6.70  thf('171', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.46/6.70         ((r1_tarski @ X0 @ X1)
% 6.46/6.70          | (zip_tseitin_0 @ X0 @ X3)
% 6.46/6.70          | (zip_tseitin_0 @ sk_B @ X2))),
% 6.46/6.70      inference('sup+', [status(thm)], ['151', '170'])).
% 6.46/6.70  thf('172', plain,
% 6.46/6.70      (![X0 : $i, X1 : $i]:
% 6.46/6.70         ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_B @ X1))),
% 6.46/6.70      inference('eq_fact', [status(thm)], ['171'])).
% 6.46/6.70  thf('173', plain,
% 6.46/6.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.46/6.70      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.46/6.70  thf('174', plain,
% 6.46/6.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k1_xboole_0)))),
% 6.46/6.70      inference('sup-', [status(thm)], ['172', '173'])).
% 6.46/6.70  thf('175', plain, (((sk_B) != (k1_xboole_0))),
% 6.46/6.70      inference('simpl_trail', [status(thm)], ['56', '131'])).
% 6.46/6.70  thf('176', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 6.46/6.70      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 6.46/6.70  thf('177', plain,
% 6.46/6.70      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 6.46/6.70      inference('demod', [status(thm)], ['150', '176'])).
% 6.46/6.70  thf('178', plain,
% 6.46/6.70      (![X0 : $i]:
% 6.46/6.70         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 6.46/6.70          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 6.46/6.70      inference('demod', [status(thm)], ['147', '177'])).
% 6.46/6.70  thf('179', plain,
% 6.46/6.70      ((((sk_C) != (sk_C))
% 6.46/6.70        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 6.46/6.70      inference('sup-', [status(thm)], ['142', '178'])).
% 6.46/6.70  thf('180', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 6.46/6.70      inference('simplify', [status(thm)], ['179'])).
% 6.46/6.70  thf('181', plain, ($false), inference('demod', [status(thm)], ['34', '180'])).
% 6.46/6.70  
% 6.46/6.70  % SZS output end Refutation
% 6.46/6.70  
% 6.46/6.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
