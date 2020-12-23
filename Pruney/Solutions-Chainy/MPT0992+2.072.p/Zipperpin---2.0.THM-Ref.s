%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5d6kCopNRr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:45 EST 2020

% Result     : Theorem 4.18s
% Output     : Refutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  229 (2942 expanded)
%              Number of leaves         :   41 ( 892 expanded)
%              Depth                    :   32
%              Number of atoms          : 1641 (33644 expanded)
%              Number of equality atoms :  117 (2612 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) ) ) ),
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

thf('17',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['37','42'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','50'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('63',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','6','7'])).

thf('65',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('67',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('82',plain,
    ( ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('84',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('94',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('105',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['92','93','105'])).

thf('107',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('110',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('112',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('113',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('114',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['92','93','105'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['74','75'])).

thf('122',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','122'])).

thf('124',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('128',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('130',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['126','132'])).

thf('134',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('135',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('137',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('138',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['65','70','77','78','79','108','109','110','111','112','133','134','135','136','139'])).

thf('141',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('142',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['140','141'])).

thf('143',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','142'])).

thf('144',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['51','143'])).

thf('145',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','144'])).

thf('146',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','142'])).

thf('147',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['24','147'])).

thf('149',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['17','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('160',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('166',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['164','169'])).

thf('171',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('174',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('175',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['153','175'])).

thf('177',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','176'])).

thf('178',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['17','152'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['164','169'])).

thf('180',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('183',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('184',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['178','184'])).

thf('186',plain,(
    $false ),
    inference(demod,[status(thm)],['177','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5d6kCopNRr
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:25 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.18/4.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.18/4.36  % Solved by: fo/fo7.sh
% 4.18/4.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.18/4.36  % done 3708 iterations in 3.888s
% 4.18/4.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.18/4.36  % SZS output start Refutation
% 4.18/4.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.18/4.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.18/4.36  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.18/4.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.18/4.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.18/4.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.18/4.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.18/4.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.18/4.36  thf(sk_B_type, type, sk_B: $i).
% 4.18/4.36  thf(sk_A_type, type, sk_A: $i).
% 4.18/4.36  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 4.18/4.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.18/4.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.18/4.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.18/4.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.18/4.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.18/4.36  thf(sk_D_type, type, sk_D: $i).
% 4.18/4.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.18/4.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.18/4.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.18/4.36  thf(sk_C_type, type, sk_C: $i).
% 4.18/4.36  thf(t38_funct_2, conjecture,
% 4.18/4.36    (![A:$i,B:$i,C:$i,D:$i]:
% 4.18/4.36     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.18/4.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.18/4.36       ( ( r1_tarski @ C @ A ) =>
% 4.18/4.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.18/4.36           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.18/4.36             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.18/4.36             ( m1_subset_1 @
% 4.18/4.36               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.18/4.36               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 4.18/4.36  thf(zf_stmt_0, negated_conjecture,
% 4.18/4.36    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.18/4.36        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.18/4.36            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.18/4.36          ( ( r1_tarski @ C @ A ) =>
% 4.18/4.36            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.18/4.36              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.18/4.36                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.18/4.36                ( m1_subset_1 @
% 4.18/4.36                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.18/4.36                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 4.18/4.36    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 4.18/4.36  thf('0', plain,
% 4.18/4.36      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 4.18/4.36        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.18/4.36             sk_B)
% 4.18/4.36        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('1', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(redefinition_k2_partfun1, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i,D:$i]:
% 4.18/4.36     ( ( ( v1_funct_1 @ C ) & 
% 4.18/4.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.18/4.36       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 4.18/4.36  thf('2', plain,
% 4.18/4.36      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.18/4.36          | ~ (v1_funct_1 @ X35)
% 4.18/4.36          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 4.18/4.36      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 4.18/4.36  thf('3', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | ~ (v1_funct_1 @ sk_D))),
% 4.18/4.36      inference('sup-', [status(thm)], ['1', '2'])).
% 4.18/4.36  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('5', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['3', '4'])).
% 4.18/4.36  thf('6', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['3', '4'])).
% 4.18/4.36  thf('7', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['3', '4'])).
% 4.18/4.36  thf('8', plain,
% 4.18/4.36      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))
% 4.18/4.36        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.18/4.36        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.18/4.36      inference('demod', [status(thm)], ['0', '5', '6', '7'])).
% 4.18/4.36  thf('9', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(dt_k2_partfun1, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i,D:$i]:
% 4.18/4.36     ( ( ( v1_funct_1 @ C ) & 
% 4.18/4.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.18/4.36       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 4.18/4.36         ( m1_subset_1 @
% 4.18/4.36           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 4.18/4.36           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.18/4.36  thf('10', plain,
% 4.18/4.36      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.18/4.36          | ~ (v1_funct_1 @ X31)
% 4.18/4.36          | (v1_funct_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34)))),
% 4.18/4.36      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.18/4.36  thf('11', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 4.18/4.36          | ~ (v1_funct_1 @ sk_D))),
% 4.18/4.36      inference('sup-', [status(thm)], ['9', '10'])).
% 4.18/4.36  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('13', plain,
% 4.18/4.36      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['11', '12'])).
% 4.18/4.36  thf('14', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['3', '4'])).
% 4.18/4.36  thf('15', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['13', '14'])).
% 4.18/4.36  thf('16', plain,
% 4.18/4.36      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.18/4.36        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.18/4.36      inference('demod', [status(thm)], ['8', '15'])).
% 4.18/4.36  thf('17', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(d1_funct_2, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i]:
% 4.18/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.18/4.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.18/4.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.18/4.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.18/4.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.18/4.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.18/4.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.18/4.36  thf(zf_stmt_1, axiom,
% 4.18/4.36    (![C:$i,B:$i,A:$i]:
% 4.18/4.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.18/4.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.18/4.36  thf('19', plain,
% 4.18/4.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.18/4.36         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 4.18/4.36          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 4.18/4.36          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.18/4.36  thf('20', plain,
% 4.18/4.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 4.18/4.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['18', '19'])).
% 4.18/4.36  thf('21', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(redefinition_k1_relset_1, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i]:
% 4.18/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.18/4.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.18/4.36  thf('22', plain,
% 4.18/4.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.18/4.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 4.18/4.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.18/4.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.18/4.36  thf('23', plain,
% 4.18/4.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.18/4.36      inference('sup-', [status(thm)], ['21', '22'])).
% 4.18/4.36  thf('24', plain,
% 4.18/4.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.18/4.36      inference('demod', [status(thm)], ['20', '23'])).
% 4.18/4.36  thf(zf_stmt_2, axiom,
% 4.18/4.36    (![B:$i,A:$i]:
% 4.18/4.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.18/4.36       ( zip_tseitin_0 @ B @ A ) ))).
% 4.18/4.36  thf('25', plain,
% 4.18/4.36      (![X23 : $i, X24 : $i]:
% 4.18/4.36         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.18/4.36  thf('26', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.18/4.36  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.18/4.36  thf(zf_stmt_5, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i]:
% 4.18/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.18/4.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.18/4.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.18/4.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.18/4.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.18/4.36  thf('27', plain,
% 4.18/4.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.18/4.36         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.18/4.36          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.18/4.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.18/4.36  thf('28', plain,
% 4.18/4.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.18/4.36      inference('sup-', [status(thm)], ['26', '27'])).
% 4.18/4.36  thf('29', plain,
% 4.18/4.36      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.18/4.36      inference('sup-', [status(thm)], ['25', '28'])).
% 4.18/4.36  thf('30', plain,
% 4.18/4.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.18/4.36      inference('demod', [status(thm)], ['20', '23'])).
% 4.18/4.36  thf('31', plain,
% 4.18/4.36      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['29', '30'])).
% 4.18/4.36  thf('32', plain,
% 4.18/4.36      (![X23 : $i, X24 : $i]:
% 4.18/4.36         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.18/4.36  thf('33', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(cc2_relset_1, axiom,
% 4.18/4.36    (![A:$i,B:$i,C:$i]:
% 4.18/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.18/4.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.18/4.36  thf('34', plain,
% 4.18/4.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.18/4.36         ((v5_relat_1 @ X17 @ X19)
% 4.18/4.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.18/4.36  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 4.18/4.36      inference('sup-', [status(thm)], ['33', '34'])).
% 4.18/4.36  thf(d19_relat_1, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( v1_relat_1 @ B ) =>
% 4.18/4.36       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.18/4.36  thf('36', plain,
% 4.18/4.36      (![X9 : $i, X10 : $i]:
% 4.18/4.36         (~ (v5_relat_1 @ X9 @ X10)
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.18/4.36          | ~ (v1_relat_1 @ X9))),
% 4.18/4.36      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.18/4.36  thf('37', plain,
% 4.18/4.36      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 4.18/4.36      inference('sup-', [status(thm)], ['35', '36'])).
% 4.18/4.36  thf('38', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf(cc2_relat_1, axiom,
% 4.18/4.36    (![A:$i]:
% 4.18/4.36     ( ( v1_relat_1 @ A ) =>
% 4.18/4.36       ( ![B:$i]:
% 4.18/4.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.18/4.36  thf('39', plain,
% 4.18/4.36      (![X7 : $i, X8 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 4.18/4.36          | (v1_relat_1 @ X7)
% 4.18/4.36          | ~ (v1_relat_1 @ X8))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.18/4.36  thf('40', plain,
% 4.18/4.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 4.18/4.36      inference('sup-', [status(thm)], ['38', '39'])).
% 4.18/4.36  thf(fc6_relat_1, axiom,
% 4.18/4.36    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.18/4.36  thf('41', plain,
% 4.18/4.36      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.18/4.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.18/4.36  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 4.18/4.36      inference('demod', [status(thm)], ['40', '41'])).
% 4.18/4.36  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 4.18/4.36      inference('demod', [status(thm)], ['37', '42'])).
% 4.18/4.36  thf(t4_funct_2, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.18/4.36       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.18/4.36         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.18/4.36           ( m1_subset_1 @
% 4.18/4.36             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.18/4.36  thf('44', plain,
% 4.18/4.36      (![X39 : $i, X40 : $i]:
% 4.18/4.36         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.18/4.36          | (m1_subset_1 @ X39 @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 4.18/4.36          | ~ (v1_funct_1 @ X39)
% 4.18/4.36          | ~ (v1_relat_1 @ X39))),
% 4.18/4.36      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.18/4.36  thf('45', plain,
% 4.18/4.36      ((~ (v1_relat_1 @ sk_D)
% 4.18/4.36        | ~ (v1_funct_1 @ sk_D)
% 4.18/4.36        | (m1_subset_1 @ sk_D @ 
% 4.18/4.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['43', '44'])).
% 4.18/4.36  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 4.18/4.36      inference('demod', [status(thm)], ['40', '41'])).
% 4.18/4.36  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('48', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ 
% 4.18/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['45', '46', '47'])).
% 4.18/4.36  thf('49', plain,
% 4.18/4.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.18/4.36         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.18/4.36          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.18/4.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.18/4.36  thf('50', plain,
% 4.18/4.36      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 4.18/4.36        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['48', '49'])).
% 4.18/4.36  thf('51', plain,
% 4.18/4.36      ((((sk_B) = (k1_xboole_0))
% 4.18/4.36        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['32', '50'])).
% 4.18/4.36  thf('52', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('53', plain,
% 4.18/4.36      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 4.18/4.36      inference('split', [status(esa)], ['52'])).
% 4.18/4.36  thf('54', plain,
% 4.18/4.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('split', [status(esa)], ['52'])).
% 4.18/4.36  thf('55', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('56', plain,
% 4.18/4.36      (((m1_subset_1 @ sk_D @ 
% 4.18/4.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 4.18/4.36         <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup+', [status(thm)], ['54', '55'])).
% 4.18/4.36  thf(t113_zfmisc_1, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.18/4.36       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.18/4.36  thf('57', plain,
% 4.18/4.36      (![X2 : $i, X3 : $i]:
% 4.18/4.36         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.18/4.36  thf('58', plain,
% 4.18/4.36      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['57'])).
% 4.18/4.36  thf('59', plain,
% 4.18/4.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 4.18/4.36         <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('demod', [status(thm)], ['56', '58'])).
% 4.18/4.36  thf(t3_subset, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.18/4.36  thf('60', plain,
% 4.18/4.36      (![X4 : $i, X5 : $i]:
% 4.18/4.36         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_subset])).
% 4.18/4.36  thf('61', plain,
% 4.18/4.36      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['59', '60'])).
% 4.18/4.36  thf(t3_xboole_1, axiom,
% 4.18/4.36    (![A:$i]:
% 4.18/4.36     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.18/4.36  thf('62', plain,
% 4.18/4.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.18/4.36  thf('63', plain,
% 4.18/4.36      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['61', '62'])).
% 4.18/4.36  thf('64', plain,
% 4.18/4.36      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))
% 4.18/4.36        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.18/4.36        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.18/4.36      inference('demod', [status(thm)], ['0', '5', '6', '7'])).
% 4.18/4.36  thf('65', plain,
% 4.18/4.36      (((~ (m1_subset_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 4.18/4.36            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 4.18/4.36         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.18/4.36         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C))))
% 4.18/4.36         <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['63', '64'])).
% 4.18/4.36  thf('66', plain,
% 4.18/4.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('split', [status(esa)], ['52'])).
% 4.18/4.36  thf('67', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('68', plain,
% 4.18/4.36      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup+', [status(thm)], ['66', '67'])).
% 4.18/4.36  thf('69', plain,
% 4.18/4.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.18/4.36  thf('70', plain,
% 4.18/4.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['68', '69'])).
% 4.18/4.36  thf(t88_relat_1, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 4.18/4.36  thf('71', plain,
% 4.18/4.36      (![X13 : $i, X14 : $i]:
% 4.18/4.36         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 4.18/4.36      inference('cnf', [status(esa)], [t88_relat_1])).
% 4.18/4.36  thf('72', plain,
% 4.18/4.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.18/4.36  thf('73', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ k1_xboole_0)
% 4.18/4.36          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['71', '72'])).
% 4.18/4.36  thf('74', plain,
% 4.18/4.36      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['57'])).
% 4.18/4.36  thf('75', plain,
% 4.18/4.36      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.18/4.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.18/4.36  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.18/4.36      inference('sup+', [status(thm)], ['74', '75'])).
% 4.18/4.36  thf('77', plain,
% 4.18/4.36      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['73', '76'])).
% 4.18/4.36  thf('78', plain,
% 4.18/4.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['68', '69'])).
% 4.18/4.36  thf('79', plain,
% 4.18/4.36      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['57'])).
% 4.18/4.36  thf('80', plain,
% 4.18/4.36      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['73', '76'])).
% 4.18/4.36  thf('81', plain,
% 4.18/4.36      (![X13 : $i, X14 : $i]:
% 4.18/4.36         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 4.18/4.36      inference('cnf', [status(esa)], [t88_relat_1])).
% 4.18/4.36  thf('82', plain,
% 4.18/4.36      (((r1_tarski @ k1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup+', [status(thm)], ['80', '81'])).
% 4.18/4.36  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.18/4.36      inference('sup+', [status(thm)], ['74', '75'])).
% 4.18/4.36  thf('84', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 4.18/4.36      inference('demod', [status(thm)], ['82', '83'])).
% 4.18/4.36  thf('85', plain,
% 4.18/4.36      (![X4 : $i, X6 : $i]:
% 4.18/4.36         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_subset])).
% 4.18/4.36  thf('86', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['84', '85'])).
% 4.18/4.36  thf('87', plain,
% 4.18/4.36      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['57'])).
% 4.18/4.36  thf('88', plain,
% 4.18/4.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.18/4.36         ((v5_relat_1 @ X17 @ X19)
% 4.18/4.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.18/4.36  thf('89', plain,
% 4.18/4.36      (![X0 : $i, X1 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.18/4.36          | (v5_relat_1 @ X1 @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['87', '88'])).
% 4.18/4.36  thf('90', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 4.18/4.36      inference('sup-', [status(thm)], ['86', '89'])).
% 4.18/4.36  thf('91', plain,
% 4.18/4.36      (![X9 : $i, X10 : $i]:
% 4.18/4.36         (~ (v5_relat_1 @ X9 @ X10)
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.18/4.36          | ~ (v1_relat_1 @ X9))),
% 4.18/4.36      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.18/4.36  thf('92', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ k1_xboole_0)
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['90', '91'])).
% 4.18/4.36  thf('93', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.18/4.36      inference('sup+', [status(thm)], ['74', '75'])).
% 4.18/4.36  thf('94', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['84', '85'])).
% 4.18/4.36  thf('95', plain,
% 4.18/4.36      (![X2 : $i, X3 : $i]:
% 4.18/4.36         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.18/4.36  thf('96', plain,
% 4.18/4.36      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['95'])).
% 4.18/4.36  thf('97', plain,
% 4.18/4.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.18/4.36         ((v5_relat_1 @ X17 @ X19)
% 4.18/4.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.18/4.36  thf('98', plain,
% 4.18/4.36      (![X1 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.18/4.36          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['96', '97'])).
% 4.18/4.36  thf('99', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 4.18/4.36      inference('sup-', [status(thm)], ['94', '98'])).
% 4.18/4.36  thf('100', plain,
% 4.18/4.36      (![X9 : $i, X10 : $i]:
% 4.18/4.36         (~ (v5_relat_1 @ X9 @ X10)
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.18/4.36          | ~ (v1_relat_1 @ X9))),
% 4.18/4.36      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.18/4.36  thf('101', plain,
% 4.18/4.36      ((~ (v1_relat_1 @ k1_xboole_0)
% 4.18/4.36        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['99', '100'])).
% 4.18/4.36  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.18/4.36      inference('sup+', [status(thm)], ['74', '75'])).
% 4.18/4.36  thf('103', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 4.18/4.36      inference('demod', [status(thm)], ['101', '102'])).
% 4.18/4.36  thf('104', plain,
% 4.18/4.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.18/4.36  thf('105', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['103', '104'])).
% 4.18/4.36  thf('106', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.18/4.36      inference('demod', [status(thm)], ['92', '93', '105'])).
% 4.18/4.36  thf('107', plain,
% 4.18/4.36      (![X4 : $i, X6 : $i]:
% 4.18/4.36         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.18/4.36      inference('cnf', [status(esa)], [t3_subset])).
% 4.18/4.36  thf('108', plain,
% 4.18/4.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['106', '107'])).
% 4.18/4.36  thf('109', plain,
% 4.18/4.36      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['61', '62'])).
% 4.18/4.36  thf('110', plain,
% 4.18/4.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['68', '69'])).
% 4.18/4.36  thf('111', plain,
% 4.18/4.36      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['73', '76'])).
% 4.18/4.36  thf('112', plain,
% 4.18/4.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['68', '69'])).
% 4.18/4.36  thf('113', plain,
% 4.18/4.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['106', '107'])).
% 4.18/4.36  thf('114', plain,
% 4.18/4.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.18/4.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 4.18/4.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.18/4.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.18/4.36  thf('115', plain,
% 4.18/4.36      (![X0 : $i, X1 : $i]:
% 4.18/4.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['113', '114'])).
% 4.18/4.36  thf('116', plain,
% 4.18/4.36      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['73', '76'])).
% 4.18/4.36  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.18/4.36      inference('demod', [status(thm)], ['92', '93', '105'])).
% 4.18/4.36  thf(t91_relat_1, axiom,
% 4.18/4.36    (![A:$i,B:$i]:
% 4.18/4.36     ( ( v1_relat_1 @ B ) =>
% 4.18/4.36       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.18/4.36         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.18/4.36  thf('118', plain,
% 4.18/4.36      (![X15 : $i, X16 : $i]:
% 4.18/4.36         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 4.18/4.36          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 4.18/4.36          | ~ (v1_relat_1 @ X16))),
% 4.18/4.36      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.18/4.36  thf('119', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ X0)
% 4.18/4.36          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['117', '118'])).
% 4.18/4.36  thf('120', plain,
% 4.18/4.36      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 4.18/4.36        | ~ (v1_relat_1 @ k1_xboole_0))),
% 4.18/4.36      inference('sup+', [status(thm)], ['116', '119'])).
% 4.18/4.36  thf('121', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.18/4.36      inference('sup+', [status(thm)], ['74', '75'])).
% 4.18/4.36  thf('122', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['120', '121'])).
% 4.18/4.36  thf('123', plain,
% 4.18/4.36      (![X0 : $i, X1 : $i]:
% 4.18/4.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['115', '122'])).
% 4.18/4.36  thf('124', plain,
% 4.18/4.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.18/4.36         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 4.18/4.36          | (v1_funct_2 @ X27 @ X25 @ X26)
% 4.18/4.36          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.18/4.36  thf('125', plain,
% 4.18/4.36      (![X0 : $i, X1 : $i]:
% 4.18/4.36         (((X1) != (k1_xboole_0))
% 4.18/4.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.18/4.36          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['123', '124'])).
% 4.18/4.36  thf('126', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.18/4.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 4.18/4.36      inference('simplify', [status(thm)], ['125'])).
% 4.18/4.36  thf('127', plain,
% 4.18/4.36      (![X23 : $i, X24 : $i]:
% 4.18/4.36         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.18/4.36  thf('128', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 4.18/4.36      inference('simplify', [status(thm)], ['127'])).
% 4.18/4.36  thf('129', plain,
% 4.18/4.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.18/4.36      inference('sup-', [status(thm)], ['106', '107'])).
% 4.18/4.36  thf('130', plain,
% 4.18/4.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.18/4.36         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.18/4.36          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.18/4.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.18/4.36  thf('131', plain,
% 4.18/4.36      (![X0 : $i, X1 : $i]:
% 4.18/4.36         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.18/4.36      inference('sup-', [status(thm)], ['129', '130'])).
% 4.18/4.36  thf('132', plain,
% 4.18/4.36      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.18/4.36      inference('sup-', [status(thm)], ['128', '131'])).
% 4.18/4.36  thf('133', plain,
% 4.18/4.36      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.18/4.36      inference('demod', [status(thm)], ['126', '132'])).
% 4.18/4.36  thf('134', plain,
% 4.18/4.36      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['61', '62'])).
% 4.18/4.36  thf('135', plain,
% 4.18/4.36      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['68', '69'])).
% 4.18/4.36  thf('136', plain,
% 4.18/4.36      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.36      inference('demod', [status(thm)], ['73', '76'])).
% 4.18/4.36  thf('137', plain,
% 4.18/4.36      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['61', '62'])).
% 4.18/4.36  thf('138', plain, ((v1_funct_1 @ sk_D)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('139', plain,
% 4.18/4.36      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.18/4.36      inference('sup+', [status(thm)], ['137', '138'])).
% 4.18/4.36  thf('140', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 4.18/4.36      inference('demod', [status(thm)],
% 4.18/4.36                ['65', '70', '77', '78', '79', '108', '109', '110', '111', 
% 4.18/4.36                 '112', '133', '134', '135', '136', '139'])).
% 4.18/4.36  thf('141', plain,
% 4.18/4.36      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 4.18/4.36      inference('split', [status(esa)], ['52'])).
% 4.18/4.36  thf('142', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 4.18/4.36      inference('sat_resolution*', [status(thm)], ['140', '141'])).
% 4.18/4.36  thf('143', plain, (((sk_B) != (k1_xboole_0))),
% 4.18/4.36      inference('simpl_trail', [status(thm)], ['53', '142'])).
% 4.18/4.36  thf('144', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 4.18/4.36      inference('simplify_reflect-', [status(thm)], ['51', '143'])).
% 4.18/4.36  thf('145', plain,
% 4.18/4.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 4.18/4.36      inference('sup+', [status(thm)], ['31', '144'])).
% 4.18/4.36  thf('146', plain, (((sk_B) != (k1_xboole_0))),
% 4.18/4.36      inference('simpl_trail', [status(thm)], ['53', '142'])).
% 4.18/4.36  thf('147', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 4.18/4.36      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 4.18/4.36  thf('148', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.18/4.36      inference('demod', [status(thm)], ['24', '147'])).
% 4.18/4.36  thf('149', plain,
% 4.18/4.36      (![X15 : $i, X16 : $i]:
% 4.18/4.36         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 4.18/4.36          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 4.18/4.36          | ~ (v1_relat_1 @ X16))),
% 4.18/4.36      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.18/4.36  thf('150', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (r1_tarski @ X0 @ sk_A)
% 4.18/4.36          | ~ (v1_relat_1 @ sk_D)
% 4.18/4.36          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['148', '149'])).
% 4.18/4.36  thf('151', plain, ((v1_relat_1 @ sk_D)),
% 4.18/4.36      inference('demod', [status(thm)], ['40', '41'])).
% 4.18/4.36  thf('152', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (r1_tarski @ X0 @ sk_A)
% 4.18/4.36          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.18/4.36      inference('demod', [status(thm)], ['150', '151'])).
% 4.18/4.36  thf('153', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 4.18/4.36      inference('sup-', [status(thm)], ['17', '152'])).
% 4.18/4.36  thf('154', plain,
% 4.18/4.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('155', plain,
% 4.18/4.36      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.18/4.36          | ~ (v1_funct_1 @ X31)
% 4.18/4.36          | (m1_subset_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34) @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 4.18/4.36      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.18/4.36  thf('156', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.18/4.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.18/4.36          | ~ (v1_funct_1 @ sk_D))),
% 4.18/4.36      inference('sup-', [status(thm)], ['154', '155'])).
% 4.18/4.36  thf('157', plain, ((v1_funct_1 @ sk_D)),
% 4.18/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.36  thf('158', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.18/4.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['156', '157'])).
% 4.18/4.36  thf('159', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['3', '4'])).
% 4.18/4.36  thf('160', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['158', '159'])).
% 4.18/4.36  thf('161', plain,
% 4.18/4.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.18/4.36         ((v5_relat_1 @ X17 @ X19)
% 4.18/4.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.18/4.36  thf('162', plain,
% 4.18/4.36      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 4.18/4.36      inference('sup-', [status(thm)], ['160', '161'])).
% 4.18/4.36  thf('163', plain,
% 4.18/4.36      (![X9 : $i, X10 : $i]:
% 4.18/4.36         (~ (v5_relat_1 @ X9 @ X10)
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.18/4.36          | ~ (v1_relat_1 @ X9))),
% 4.18/4.36      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.18/4.36  thf('164', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.18/4.36      inference('sup-', [status(thm)], ['162', '163'])).
% 4.18/4.36  thf('165', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['158', '159'])).
% 4.18/4.36  thf('166', plain,
% 4.18/4.36      (![X7 : $i, X8 : $i]:
% 4.18/4.36         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 4.18/4.36          | (v1_relat_1 @ X7)
% 4.18/4.36          | ~ (v1_relat_1 @ X8))),
% 4.18/4.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.18/4.36  thf('167', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.18/4.36          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 4.18/4.36      inference('sup-', [status(thm)], ['165', '166'])).
% 4.18/4.36  thf('168', plain,
% 4.18/4.36      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.18/4.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.18/4.36  thf('169', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['167', '168'])).
% 4.18/4.36  thf('170', plain,
% 4.18/4.36      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.18/4.36      inference('demod', [status(thm)], ['164', '169'])).
% 4.18/4.36  thf('171', plain,
% 4.18/4.36      (![X39 : $i, X40 : $i]:
% 4.18/4.36         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.18/4.36          | (v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ X40)
% 4.18/4.36          | ~ (v1_funct_1 @ X39)
% 4.18/4.36          | ~ (v1_relat_1 @ X39))),
% 4.18/4.36      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.18/4.36  thf('172', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.18/4.36      inference('sup-', [status(thm)], ['170', '171'])).
% 4.18/4.36  thf('173', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['167', '168'])).
% 4.18/4.36  thf('174', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['13', '14'])).
% 4.18/4.36  thf('175', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.18/4.36      inference('demod', [status(thm)], ['172', '173', '174'])).
% 4.18/4.36  thf('176', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 4.18/4.36      inference('sup+', [status(thm)], ['153', '175'])).
% 4.18/4.36  thf('177', plain,
% 4.18/4.36      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.18/4.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['16', '176'])).
% 4.18/4.36  thf('178', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 4.18/4.36      inference('sup-', [status(thm)], ['17', '152'])).
% 4.18/4.36  thf('179', plain,
% 4.18/4.36      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.18/4.36      inference('demod', [status(thm)], ['164', '169'])).
% 4.18/4.36  thf('180', plain,
% 4.18/4.36      (![X39 : $i, X40 : $i]:
% 4.18/4.36         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.18/4.36          | (m1_subset_1 @ X39 @ 
% 4.18/4.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 4.18/4.36          | ~ (v1_funct_1 @ X39)
% 4.18/4.36          | ~ (v1_relat_1 @ X39))),
% 4.18/4.36      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.18/4.36  thf('181', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.18/4.36          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36             (k1_zfmisc_1 @ 
% 4.18/4.36              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 4.18/4.36      inference('sup-', [status(thm)], ['179', '180'])).
% 4.18/4.36  thf('182', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['167', '168'])).
% 4.18/4.36  thf('183', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.18/4.36      inference('demod', [status(thm)], ['13', '14'])).
% 4.18/4.36  thf('184', plain,
% 4.18/4.36      (![X0 : $i]:
% 4.18/4.36         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.18/4.36          (k1_zfmisc_1 @ 
% 4.18/4.36           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 4.18/4.36      inference('demod', [status(thm)], ['181', '182', '183'])).
% 4.18/4.36  thf('185', plain,
% 4.18/4.36      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.18/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.18/4.36      inference('sup+', [status(thm)], ['178', '184'])).
% 4.18/4.36  thf('186', plain, ($false), inference('demod', [status(thm)], ['177', '185'])).
% 4.18/4.36  
% 4.18/4.36  % SZS output end Refutation
% 4.18/4.36  
% 4.18/4.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
