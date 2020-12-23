%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3OT0djGpD3

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:37 EST 2020

% Result     : Theorem 52.30s
% Output     : Refutation 52.30s
% Verified   : 
% Statistics : Number of formulae       :  231 (1206 expanded)
%              Number of leaves         :   46 ( 365 expanded)
%              Depth                    :   21
%              Number of atoms          : 1670 (18052 expanded)
%              Number of equality atoms :  131 (1202 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 )
        = ( k7_relat_1 @ X45 @ X48 ) ) ) ),
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
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['32','35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_relat_1 @ sk_D )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['43','58'])).

thf('60',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('64',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('72',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X29 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('73',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('80',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('87',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('89',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('90',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('91',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('92',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','78','85','86','87','88','89','90','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('97',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('100',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('105',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('106',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('108',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('111',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('112',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('113',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('121',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('123',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['119','125'])).

thf('127',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['92','98','108','109','110','111','126'])).

thf('128',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('129',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','130'])).

thf('132',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('133',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('137',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['131','142'])).

thf('144',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','143'])).

thf('145',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','144'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('146',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('163',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['161','164'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('166',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('169',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('171',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['167','168','171'])).

thf('173',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['150','172'])).

thf('174',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','173'])).

thf('175',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','149'])).

thf('176',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['161','164'])).

thf('177',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('180',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('181',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['175','181'])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['174','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3OT0djGpD3
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:22:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 52.30/52.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 52.30/52.55  % Solved by: fo/fo7.sh
% 52.30/52.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 52.30/52.55  % done 44866 iterations in 52.112s
% 52.30/52.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 52.30/52.55  % SZS output start Refutation
% 52.30/52.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 52.30/52.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 52.30/52.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 52.30/52.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 52.30/52.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 52.30/52.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 52.30/52.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 52.30/52.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 52.30/52.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 52.30/52.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 52.30/52.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 52.30/52.55  thf(sk_A_type, type, sk_A: $i).
% 52.30/52.55  thf(sk_D_type, type, sk_D: $i).
% 52.30/52.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 52.30/52.55  thf(sk_C_type, type, sk_C: $i).
% 52.30/52.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 52.30/52.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 52.30/52.55  thf(sk_B_type, type, sk_B: $i).
% 52.30/52.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 52.30/52.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 52.30/52.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 52.30/52.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 52.30/52.55  thf(t38_funct_2, conjecture,
% 52.30/52.55    (![A:$i,B:$i,C:$i,D:$i]:
% 52.30/52.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 52.30/52.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.30/52.55       ( ( r1_tarski @ C @ A ) =>
% 52.30/52.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 52.30/52.55           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 52.30/52.55             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 52.30/52.55             ( m1_subset_1 @
% 52.30/52.55               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 52.30/52.55               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 52.30/52.55  thf(zf_stmt_0, negated_conjecture,
% 52.30/52.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 52.30/52.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 52.30/52.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.30/52.55          ( ( r1_tarski @ C @ A ) =>
% 52.30/52.55            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 52.30/52.55              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 52.30/52.55                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 52.30/52.55                ( m1_subset_1 @
% 52.30/52.55                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 52.30/52.55                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 52.30/52.55    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 52.30/52.55  thf('0', plain,
% 52.30/52.55      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 52.30/52.55        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 52.30/52.55             sk_B)
% 52.30/52.55        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 52.30/52.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf('1', plain,
% 52.30/52.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf(dt_k2_partfun1, axiom,
% 52.30/52.55    (![A:$i,B:$i,C:$i,D:$i]:
% 52.30/52.55     ( ( ( v1_funct_1 @ C ) & 
% 52.30/52.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.30/52.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 52.30/52.55         ( m1_subset_1 @
% 52.30/52.55           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 52.30/52.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 52.30/52.55  thf('2', plain,
% 52.30/52.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 52.30/52.55         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 52.30/52.55          | ~ (v1_funct_1 @ X41)
% 52.30/52.55          | (v1_funct_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44)))),
% 52.30/52.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 52.30/52.55  thf('3', plain,
% 52.30/52.55      (![X0 : $i]:
% 52.30/52.55         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 52.30/52.55          | ~ (v1_funct_1 @ sk_D))),
% 52.30/52.55      inference('sup-', [status(thm)], ['1', '2'])).
% 52.30/52.55  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf('5', plain,
% 52.30/52.55      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 52.30/52.55      inference('demod', [status(thm)], ['3', '4'])).
% 52.30/52.55  thf('6', plain,
% 52.30/52.55      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.30/52.55        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 52.30/52.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.30/52.55      inference('demod', [status(thm)], ['0', '5'])).
% 52.30/52.55  thf('7', plain,
% 52.30/52.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf(redefinition_k2_partfun1, axiom,
% 52.30/52.55    (![A:$i,B:$i,C:$i,D:$i]:
% 52.30/52.55     ( ( ( v1_funct_1 @ C ) & 
% 52.30/52.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.30/52.55       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 52.30/52.55  thf('8', plain,
% 52.30/52.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 52.30/52.55         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 52.30/52.55          | ~ (v1_funct_1 @ X45)
% 52.30/52.55          | ((k2_partfun1 @ X46 @ X47 @ X45 @ X48) = (k7_relat_1 @ X45 @ X48)))),
% 52.30/52.55      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 52.30/52.55  thf('9', plain,
% 52.30/52.55      (![X0 : $i]:
% 52.30/52.55         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 52.30/52.55          | ~ (v1_funct_1 @ sk_D))),
% 52.30/52.55      inference('sup-', [status(thm)], ['7', '8'])).
% 52.30/52.55  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf('11', plain,
% 52.30/52.55      (![X0 : $i]:
% 52.30/52.55         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.55      inference('demod', [status(thm)], ['9', '10'])).
% 52.30/52.55  thf('12', plain,
% 52.30/52.55      (![X0 : $i]:
% 52.30/52.55         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.55      inference('demod', [status(thm)], ['9', '10'])).
% 52.30/52.55  thf('13', plain,
% 52.30/52.55      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.30/52.55        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.30/52.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.30/52.55      inference('demod', [status(thm)], ['6', '11', '12'])).
% 52.30/52.55  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.55  thf(d1_funct_2, axiom,
% 52.30/52.55    (![A:$i,B:$i,C:$i]:
% 52.30/52.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 52.30/52.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 52.30/52.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 52.30/52.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 52.30/52.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 52.30/52.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 52.30/52.55  thf(zf_stmt_1, axiom,
% 52.30/52.55    (![C:$i,B:$i,A:$i]:
% 52.30/52.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 52.30/52.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 52.30/52.55  thf('16', plain,
% 52.30/52.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 52.30/52.55         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 52.30/52.55          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 52.30/52.55          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 52.30/52.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 52.30/52.55  thf('17', plain,
% 52.30/52.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 52.30/52.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['15', '16'])).
% 52.30/52.56  thf('18', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf(redefinition_k1_relset_1, axiom,
% 52.30/52.56    (![A:$i,B:$i,C:$i]:
% 52.30/52.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 52.30/52.56  thf('19', plain,
% 52.30/52.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 52.30/52.56         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 52.30/52.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 52.30/52.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 52.30/52.56  thf('20', plain,
% 52.30/52.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 52.30/52.56      inference('sup-', [status(thm)], ['18', '19'])).
% 52.30/52.56  thf('21', plain,
% 52.30/52.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.30/52.56      inference('demod', [status(thm)], ['17', '20'])).
% 52.30/52.56  thf('22', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 52.30/52.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 52.30/52.56  thf(zf_stmt_4, axiom,
% 52.30/52.56    (![B:$i,A:$i]:
% 52.30/52.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 52.30/52.56       ( zip_tseitin_0 @ B @ A ) ))).
% 52.30/52.56  thf(zf_stmt_5, axiom,
% 52.30/52.56    (![A:$i,B:$i,C:$i]:
% 52.30/52.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 52.30/52.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 52.30/52.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 52.30/52.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 52.30/52.56  thf('23', plain,
% 52.30/52.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 52.30/52.56         (~ (zip_tseitin_0 @ X38 @ X39)
% 52.30/52.56          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 52.30/52.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 52.30/52.56  thf('24', plain,
% 52.30/52.56      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 52.30/52.56      inference('sup-', [status(thm)], ['22', '23'])).
% 52.30/52.56  thf('25', plain,
% 52.30/52.56      (![X33 : $i, X34 : $i]:
% 52.30/52.56         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 52.30/52.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 52.30/52.56  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 52.30/52.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 52.30/52.56  thf('27', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 52.30/52.56      inference('sup+', [status(thm)], ['25', '26'])).
% 52.30/52.56  thf('28', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf(cc2_relset_1, axiom,
% 52.30/52.56    (![A:$i,B:$i,C:$i]:
% 52.30/52.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 52.30/52.56  thf('29', plain,
% 52.30/52.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 52.30/52.56         ((v5_relat_1 @ X24 @ X26)
% 52.30/52.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 52.30/52.56  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 52.30/52.56      inference('sup-', [status(thm)], ['28', '29'])).
% 52.30/52.56  thf(d19_relat_1, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( v1_relat_1 @ B ) =>
% 52.30/52.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 52.30/52.56  thf('31', plain,
% 52.30/52.56      (![X12 : $i, X13 : $i]:
% 52.30/52.56         (~ (v5_relat_1 @ X12 @ X13)
% 52.30/52.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 52.30/52.56          | ~ (v1_relat_1 @ X12))),
% 52.30/52.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 52.30/52.56  thf('32', plain,
% 52.30/52.56      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 52.30/52.56      inference('sup-', [status(thm)], ['30', '31'])).
% 52.30/52.56  thf('33', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf(cc1_relset_1, axiom,
% 52.30/52.56    (![A:$i,B:$i,C:$i]:
% 52.30/52.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.56       ( v1_relat_1 @ C ) ))).
% 52.30/52.56  thf('34', plain,
% 52.30/52.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 52.30/52.56         ((v1_relat_1 @ X21)
% 52.30/52.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.30/52.56  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 52.30/52.56      inference('sup-', [status(thm)], ['33', '34'])).
% 52.30/52.56  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 52.30/52.56      inference('demod', [status(thm)], ['32', '35'])).
% 52.30/52.56  thf(l13_xboole_0, axiom,
% 52.30/52.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 52.30/52.56  thf('37', plain,
% 52.30/52.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 52.30/52.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 52.30/52.56  thf('38', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 52.30/52.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 52.30/52.56  thf('39', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('sup+', [status(thm)], ['37', '38'])).
% 52.30/52.56  thf(d10_xboole_0, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 52.30/52.56  thf('40', plain,
% 52.30/52.56      (![X1 : $i, X3 : $i]:
% 52.30/52.56         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 52.30/52.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 52.30/52.56  thf('41', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['39', '40'])).
% 52.30/52.56  thf('42', plain, ((((k2_relat_1 @ sk_D) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 52.30/52.56      inference('sup-', [status(thm)], ['36', '41'])).
% 52.30/52.56  thf('43', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_relat_1 @ sk_D) = (sk_B)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['27', '42'])).
% 52.30/52.56  thf('44', plain,
% 52.30/52.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 52.30/52.56  thf(t4_subset_1, axiom,
% 52.30/52.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 52.30/52.56  thf('45', plain,
% 52.30/52.56      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.30/52.56  thf('46', plain,
% 52.30/52.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 52.30/52.56         ((v5_relat_1 @ X24 @ X26)
% 52.30/52.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 52.30/52.56  thf('47', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 52.30/52.56      inference('sup-', [status(thm)], ['45', '46'])).
% 52.30/52.56  thf('48', plain,
% 52.30/52.56      (![X12 : $i, X13 : $i]:
% 52.30/52.56         (~ (v5_relat_1 @ X12 @ X13)
% 52.30/52.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 52.30/52.56          | ~ (v1_relat_1 @ X12))),
% 52.30/52.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 52.30/52.56  thf('49', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (v1_relat_1 @ k1_xboole_0)
% 52.30/52.56          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['47', '48'])).
% 52.30/52.56  thf('50', plain,
% 52.30/52.56      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.30/52.56  thf('51', plain,
% 52.30/52.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 52.30/52.56         ((v1_relat_1 @ X21)
% 52.30/52.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.30/52.56  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 52.30/52.56      inference('sup-', [status(thm)], ['50', '51'])).
% 52.30/52.56  thf('53', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 52.30/52.56      inference('demod', [status(thm)], ['49', '52'])).
% 52.30/52.56  thf('54', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 52.30/52.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 52.30/52.56  thf('55', plain,
% 52.30/52.56      (![X1 : $i, X3 : $i]:
% 52.30/52.56         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 52.30/52.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 52.30/52.56  thf('56', plain,
% 52.30/52.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['54', '55'])).
% 52.30/52.56  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['53', '56'])).
% 52.30/52.56  thf('58', plain,
% 52.30/52.56      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('sup+', [status(thm)], ['44', '57'])).
% 52.30/52.56  thf('59', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (((sk_B) = (k1_xboole_0))
% 52.30/52.56          | (zip_tseitin_0 @ sk_B @ X0)
% 52.30/52.56          | ~ (v1_xboole_0 @ sk_D))),
% 52.30/52.56      inference('sup+', [status(thm)], ['43', '58'])).
% 52.30/52.56  thf('60', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('61', plain,
% 52.30/52.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('62', plain,
% 52.30/52.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('63', plain,
% 52.30/52.56      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.30/52.56        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 52.30/52.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.30/52.56      inference('demod', [status(thm)], ['0', '5'])).
% 52.30/52.56  thf('64', plain,
% 52.30/52.56      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 52.30/52.56            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 52.30/52.56         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 52.30/52.56              sk_B)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['62', '63'])).
% 52.30/52.56  thf('65', plain,
% 52.30/52.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('66', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('67', plain,
% 52.30/52.56      (((m1_subset_1 @ sk_D @ 
% 52.30/52.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup+', [status(thm)], ['65', '66'])).
% 52.30/52.56  thf(t113_zfmisc_1, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 52.30/52.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 52.30/52.56  thf('68', plain,
% 52.30/52.56      (![X6 : $i, X7 : $i]:
% 52.30/52.56         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 52.30/52.56  thf('69', plain,
% 52.30/52.56      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['68'])).
% 52.30/52.56  thf('70', plain,
% 52.30/52.56      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['67', '69'])).
% 52.30/52.56  thf('71', plain,
% 52.30/52.56      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['68'])).
% 52.30/52.56  thf(cc3_relset_1, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( v1_xboole_0 @ A ) =>
% 52.30/52.56       ( ![C:$i]:
% 52.30/52.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.30/52.56           ( v1_xboole_0 @ C ) ) ) ))).
% 52.30/52.56  thf('72', plain,
% 52.30/52.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 52.30/52.56         (~ (v1_xboole_0 @ X27)
% 52.30/52.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X29)))
% 52.30/52.56          | (v1_xboole_0 @ X28))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc3_relset_1])).
% 52.30/52.56  thf('73', plain,
% 52.30/52.56      (![X1 : $i]:
% 52.30/52.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 52.30/52.56          | (v1_xboole_0 @ X1)
% 52.30/52.56          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['71', '72'])).
% 52.30/52.56  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 52.30/52.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 52.30/52.56  thf('75', plain,
% 52.30/52.56      (![X1 : $i]:
% 52.30/52.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 52.30/52.56          | (v1_xboole_0 @ X1))),
% 52.30/52.56      inference('demod', [status(thm)], ['73', '74'])).
% 52.30/52.56  thf('76', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['70', '75'])).
% 52.30/52.56  thf('77', plain,
% 52.30/52.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 52.30/52.56  thf('78', plain,
% 52.30/52.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['76', '77'])).
% 52.30/52.56  thf('79', plain,
% 52.30/52.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('80', plain, ((r1_tarski @ sk_C @ sk_A)),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('81', plain,
% 52.30/52.56      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup+', [status(thm)], ['79', '80'])).
% 52.30/52.56  thf('82', plain,
% 52.30/52.56      (![X1 : $i, X3 : $i]:
% 52.30/52.56         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 52.30/52.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 52.30/52.56  thf('83', plain,
% 52.30/52.56      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['81', '82'])).
% 52.30/52.56  thf('84', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 52.30/52.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 52.30/52.56  thf('85', plain,
% 52.30/52.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['83', '84'])).
% 52.30/52.56  thf('86', plain,
% 52.30/52.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['83', '84'])).
% 52.30/52.56  thf('87', plain,
% 52.30/52.56      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['68'])).
% 52.30/52.56  thf('88', plain,
% 52.30/52.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('89', plain,
% 52.30/52.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['76', '77'])).
% 52.30/52.56  thf('90', plain,
% 52.30/52.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['83', '84'])).
% 52.30/52.56  thf('91', plain,
% 52.30/52.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['83', '84'])).
% 52.30/52.56  thf('92', plain,
% 52.30/52.56      (((~ (m1_subset_1 @ 
% 52.30/52.56            (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 52.30/52.56            (k1_zfmisc_1 @ k1_xboole_0))
% 52.30/52.56         | ~ (v1_funct_2 @ 
% 52.30/52.56              (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 52.30/52.56              k1_xboole_0 @ sk_B)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)],
% 52.30/52.56                ['64', '78', '85', '86', '87', '88', '89', '90', '91'])).
% 52.30/52.56  thf('93', plain,
% 52.30/52.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('94', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['9', '10'])).
% 52.30/52.56  thf('95', plain,
% 52.30/52.56      ((![X0 : $i]:
% 52.30/52.56          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0)
% 52.30/52.56            = (k7_relat_1 @ sk_D @ X0)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup+', [status(thm)], ['93', '94'])).
% 52.30/52.56  thf('96', plain,
% 52.30/52.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['76', '77'])).
% 52.30/52.56  thf('97', plain,
% 52.30/52.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['76', '77'])).
% 52.30/52.56  thf('98', plain,
% 52.30/52.56      ((![X0 : $i]:
% 52.30/52.56          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0)
% 52.30/52.56            = (k7_relat_1 @ k1_xboole_0 @ X0)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['95', '96', '97'])).
% 52.30/52.56  thf('99', plain,
% 52.30/52.56      (![X6 : $i, X7 : $i]:
% 52.30/52.56         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 52.30/52.56  thf('100', plain,
% 52.30/52.56      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['99'])).
% 52.30/52.56  thf(t193_relat_1, axiom,
% 52.30/52.56    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 52.30/52.56  thf('101', plain,
% 52.30/52.56      (![X16 : $i, X17 : $i]:
% 52.30/52.56         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17)) @ X16)),
% 52.30/52.56      inference('cnf', [status(esa)], [t193_relat_1])).
% 52.30/52.56  thf('102', plain,
% 52.30/52.56      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 52.30/52.56      inference('sup+', [status(thm)], ['100', '101'])).
% 52.30/52.56  thf('103', plain,
% 52.30/52.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['54', '55'])).
% 52.30/52.56  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['102', '103'])).
% 52.30/52.56  thf(t98_relat_1, axiom,
% 52.30/52.56    (![A:$i]:
% 52.30/52.56     ( ( v1_relat_1 @ A ) =>
% 52.30/52.56       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 52.30/52.56  thf('105', plain,
% 52.30/52.56      (![X20 : $i]:
% 52.30/52.56         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 52.30/52.56          | ~ (v1_relat_1 @ X20))),
% 52.30/52.56      inference('cnf', [status(esa)], [t98_relat_1])).
% 52.30/52.56  thf('106', plain,
% 52.30/52.56      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 52.30/52.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 52.30/52.56      inference('sup+', [status(thm)], ['104', '105'])).
% 52.30/52.56  thf('107', plain, ((v1_relat_1 @ k1_xboole_0)),
% 52.30/52.56      inference('sup-', [status(thm)], ['50', '51'])).
% 52.30/52.56  thf('108', plain,
% 52.30/52.56      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('demod', [status(thm)], ['106', '107'])).
% 52.30/52.56  thf('109', plain,
% 52.30/52.56      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.30/52.56  thf('110', plain,
% 52.30/52.56      ((![X0 : $i]:
% 52.30/52.56          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0)
% 52.30/52.56            = (k7_relat_1 @ k1_xboole_0 @ X0)))
% 52.30/52.56         <= ((((sk_A) = (k1_xboole_0))))),
% 52.30/52.56      inference('demod', [status(thm)], ['95', '96', '97'])).
% 52.30/52.56  thf('111', plain,
% 52.30/52.56      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('demod', [status(thm)], ['106', '107'])).
% 52.30/52.56  thf('112', plain,
% 52.30/52.56      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.30/52.56  thf('113', plain,
% 52.30/52.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 52.30/52.56         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 52.30/52.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 52.30/52.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 52.30/52.56  thf('114', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['112', '113'])).
% 52.30/52.56  thf('115', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['102', '103'])).
% 52.30/52.56  thf('116', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('demod', [status(thm)], ['114', '115'])).
% 52.30/52.56  thf('117', plain,
% 52.30/52.56      (![X35 : $i, X36 : $i, X37 : $i]:
% 52.30/52.56         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 52.30/52.56          | (v1_funct_2 @ X37 @ X35 @ X36)
% 52.30/52.56          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 52.30/52.56  thf('118', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         (((X1) != (k1_xboole_0))
% 52.30/52.56          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 52.30/52.56          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['116', '117'])).
% 52.30/52.56  thf('119', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 52.30/52.56          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['118'])).
% 52.30/52.56  thf('120', plain,
% 52.30/52.56      (![X33 : $i, X34 : $i]:
% 52.30/52.56         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 52.30/52.56  thf('121', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 52.30/52.56      inference('simplify', [status(thm)], ['120'])).
% 52.30/52.56  thf('122', plain,
% 52.30/52.56      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.30/52.56  thf('123', plain,
% 52.30/52.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 52.30/52.56         (~ (zip_tseitin_0 @ X38 @ X39)
% 52.30/52.56          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 52.30/52.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 52.30/52.56  thf('124', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 52.30/52.56      inference('sup-', [status(thm)], ['122', '123'])).
% 52.30/52.56  thf('125', plain,
% 52.30/52.56      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 52.30/52.56      inference('sup-', [status(thm)], ['121', '124'])).
% 52.30/52.56  thf('126', plain,
% 52.30/52.56      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 52.30/52.56      inference('demod', [status(thm)], ['119', '125'])).
% 52.30/52.56  thf('127', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 52.30/52.56      inference('demod', [status(thm)],
% 52.30/52.56                ['92', '98', '108', '109', '110', '111', '126'])).
% 52.30/52.56  thf('128', plain,
% 52.30/52.56      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 52.30/52.56      inference('split', [status(esa)], ['60'])).
% 52.30/52.56  thf('129', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 52.30/52.56      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 52.30/52.56  thf('130', plain, (((sk_B) != (k1_xboole_0))),
% 52.30/52.56      inference('simpl_trail', [status(thm)], ['61', '129'])).
% 52.30/52.56  thf('131', plain,
% 52.30/52.56      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 52.30/52.56      inference('simplify_reflect-', [status(thm)], ['59', '130'])).
% 52.30/52.56  thf('132', plain,
% 52.30/52.56      (![X33 : $i, X34 : $i]:
% 52.30/52.56         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 52.30/52.56  thf('133', plain,
% 52.30/52.56      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 52.30/52.56      inference('simplify', [status(thm)], ['99'])).
% 52.30/52.56  thf('134', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.30/52.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 52.30/52.56      inference('sup+', [status(thm)], ['132', '133'])).
% 52.30/52.56  thf('135', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('136', plain,
% 52.30/52.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 52.30/52.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 52.30/52.56  thf('137', plain,
% 52.30/52.56      (![X1 : $i]:
% 52.30/52.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 52.30/52.56          | (v1_xboole_0 @ X1))),
% 52.30/52.56      inference('demod', [status(thm)], ['73', '74'])).
% 52.30/52.56  thf('138', plain,
% 52.30/52.56      (![X0 : $i, X1 : $i]:
% 52.30/52.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 52.30/52.56          | ~ (v1_xboole_0 @ X0)
% 52.30/52.56          | (v1_xboole_0 @ X1))),
% 52.30/52.56      inference('sup-', [status(thm)], ['136', '137'])).
% 52.30/52.56  thf('139', plain,
% 52.30/52.56      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['135', '138'])).
% 52.30/52.56  thf('140', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 52.30/52.56          | (zip_tseitin_0 @ sk_B @ X0)
% 52.30/52.56          | (v1_xboole_0 @ sk_D))),
% 52.30/52.56      inference('sup-', [status(thm)], ['134', '139'])).
% 52.30/52.56  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 52.30/52.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 52.30/52.56  thf('142', plain,
% 52.30/52.56      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D))),
% 52.30/52.56      inference('demod', [status(thm)], ['140', '141'])).
% 52.30/52.56  thf('143', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 52.30/52.56      inference('clc', [status(thm)], ['131', '142'])).
% 52.30/52.56  thf('144', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 52.30/52.56      inference('demod', [status(thm)], ['24', '143'])).
% 52.30/52.56  thf('145', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 52.30/52.56      inference('demod', [status(thm)], ['21', '144'])).
% 52.30/52.56  thf(t91_relat_1, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( v1_relat_1 @ B ) =>
% 52.30/52.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 52.30/52.56         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 52.30/52.56  thf('146', plain,
% 52.30/52.56      (![X18 : $i, X19 : $i]:
% 52.30/52.56         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 52.30/52.56          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 52.30/52.56          | ~ (v1_relat_1 @ X19))),
% 52.30/52.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 52.30/52.56  thf('147', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (r1_tarski @ X0 @ sk_A)
% 52.30/52.56          | ~ (v1_relat_1 @ sk_D)
% 52.30/52.56          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 52.30/52.56      inference('sup-', [status(thm)], ['145', '146'])).
% 52.30/52.56  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 52.30/52.56      inference('sup-', [status(thm)], ['33', '34'])).
% 52.30/52.56  thf('149', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (r1_tarski @ X0 @ sk_A)
% 52.30/52.56          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 52.30/52.56      inference('demod', [status(thm)], ['147', '148'])).
% 52.30/52.56  thf('150', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 52.30/52.56      inference('sup-', [status(thm)], ['14', '149'])).
% 52.30/52.56  thf('151', plain,
% 52.30/52.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('152', plain,
% 52.30/52.56      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 52.30/52.56         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 52.30/52.56          | ~ (v1_funct_1 @ X41)
% 52.30/52.56          | (m1_subset_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44) @ 
% 52.30/52.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 52.30/52.56      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 52.30/52.56  thf('153', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 52.30/52.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 52.30/52.56          | ~ (v1_funct_1 @ sk_D))),
% 52.30/52.56      inference('sup-', [status(thm)], ['151', '152'])).
% 52.30/52.56  thf('154', plain, ((v1_funct_1 @ sk_D)),
% 52.30/52.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.30/52.56  thf('155', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 52.30/52.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('demod', [status(thm)], ['153', '154'])).
% 52.30/52.56  thf('156', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['9', '10'])).
% 52.30/52.56  thf('157', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('demod', [status(thm)], ['155', '156'])).
% 52.30/52.56  thf('158', plain,
% 52.30/52.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 52.30/52.56         ((v5_relat_1 @ X24 @ X26)
% 52.30/52.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 52.30/52.56  thf('159', plain,
% 52.30/52.56      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 52.30/52.56      inference('sup-', [status(thm)], ['157', '158'])).
% 52.30/52.56  thf('160', plain,
% 52.30/52.56      (![X12 : $i, X13 : $i]:
% 52.30/52.56         (~ (v5_relat_1 @ X12 @ X13)
% 52.30/52.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 52.30/52.56          | ~ (v1_relat_1 @ X12))),
% 52.30/52.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 52.30/52.56  thf('161', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.30/52.56          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 52.30/52.56      inference('sup-', [status(thm)], ['159', '160'])).
% 52.30/52.56  thf('162', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.30/52.56      inference('demod', [status(thm)], ['155', '156'])).
% 52.30/52.56  thf('163', plain,
% 52.30/52.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 52.30/52.56         ((v1_relat_1 @ X21)
% 52.30/52.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 52.30/52.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.30/52.56  thf('164', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['162', '163'])).
% 52.30/52.56  thf('165', plain,
% 52.30/52.56      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.30/52.56      inference('demod', [status(thm)], ['161', '164'])).
% 52.30/52.56  thf(t4_funct_2, axiom,
% 52.30/52.56    (![A:$i,B:$i]:
% 52.30/52.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 52.30/52.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 52.30/52.56         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 52.30/52.56           ( m1_subset_1 @
% 52.30/52.56             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 52.30/52.56  thf('166', plain,
% 52.30/52.56      (![X49 : $i, X50 : $i]:
% 52.30/52.56         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 52.30/52.56          | (v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ X50)
% 52.30/52.56          | ~ (v1_funct_1 @ X49)
% 52.30/52.56          | ~ (v1_relat_1 @ X49))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_funct_2])).
% 52.30/52.56  thf('167', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.30/52.56          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.30/52.56          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 52.30/52.56      inference('sup-', [status(thm)], ['165', '166'])).
% 52.30/52.56  thf('168', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['162', '163'])).
% 52.30/52.56  thf('169', plain,
% 52.30/52.56      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['3', '4'])).
% 52.30/52.56  thf('170', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['9', '10'])).
% 52.30/52.56  thf('171', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['169', '170'])).
% 52.30/52.56  thf('172', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.30/52.56      inference('demod', [status(thm)], ['167', '168', '171'])).
% 52.30/52.56  thf('173', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 52.30/52.56      inference('sup+', [status(thm)], ['150', '172'])).
% 52.30/52.56  thf('174', plain,
% 52.30/52.56      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.30/52.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 52.30/52.56      inference('demod', [status(thm)], ['13', '173'])).
% 52.30/52.56  thf('175', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 52.30/52.56      inference('sup-', [status(thm)], ['14', '149'])).
% 52.30/52.56  thf('176', plain,
% 52.30/52.56      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.30/52.56      inference('demod', [status(thm)], ['161', '164'])).
% 52.30/52.56  thf('177', plain,
% 52.30/52.56      (![X49 : $i, X50 : $i]:
% 52.30/52.56         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 52.30/52.56          | (m1_subset_1 @ X49 @ 
% 52.30/52.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ X50)))
% 52.30/52.56          | ~ (v1_funct_1 @ X49)
% 52.30/52.56          | ~ (v1_relat_1 @ X49))),
% 52.30/52.56      inference('cnf', [status(esa)], [t4_funct_2])).
% 52.30/52.56  thf('178', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.30/52.56          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.30/52.56          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56             (k1_zfmisc_1 @ 
% 52.30/52.56              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 52.30/52.56      inference('sup-', [status(thm)], ['176', '177'])).
% 52.30/52.56  thf('179', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('sup-', [status(thm)], ['162', '163'])).
% 52.30/52.56  thf('180', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.30/52.56      inference('demod', [status(thm)], ['169', '170'])).
% 52.30/52.56  thf('181', plain,
% 52.30/52.56      (![X0 : $i]:
% 52.30/52.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.30/52.56          (k1_zfmisc_1 @ 
% 52.30/52.56           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 52.30/52.56      inference('demod', [status(thm)], ['178', '179', '180'])).
% 52.30/52.56  thf('182', plain,
% 52.30/52.56      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.30/52.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 52.30/52.56      inference('sup+', [status(thm)], ['175', '181'])).
% 52.30/52.56  thf('183', plain, ($false), inference('demod', [status(thm)], ['174', '182'])).
% 52.30/52.56  
% 52.30/52.56  % SZS output end Refutation
% 52.30/52.56  
% 52.39/52.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
