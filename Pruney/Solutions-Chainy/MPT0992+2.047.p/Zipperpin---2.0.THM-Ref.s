%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ksqZns0y9l

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:41 EST 2020

% Result     : Theorem 30.52s
% Output     : Refutation 30.52s
% Verified   : 
% Statistics : Number of formulae       :  304 (2083 expanded)
%              Number of leaves         :   46 ( 632 expanded)
%              Depth                    :   23
%              Number of atoms          : 2455 (32078 expanded)
%              Number of equality atoms :  210 (2057 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 )
        = ( k7_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('17',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) )
      = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) )
          = sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_C )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

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

thf('58',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','72','73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('77',plain,
    ( ( ( ( k7_relat_1 @ sk_D @ k1_xboole_0 )
        = sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k7_relat_1 @ sk_D @ k1_xboole_0 )
      = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relat_1 @ sk_D @ X0 )
          = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
        | ~ ( v1_relat_1 @ sk_D )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k7_relat_1 @ sk_D @ k1_xboole_0 )
      = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('95',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','87','107'])).

thf('109',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( k7_relat_1 @ sk_D @ X0 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('117',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','92'])).

thf('118',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('120',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('126',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('128',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['135','136'])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('138',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
      | ~ ( v5_relat_1 @ X21 @ X23 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('141',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['135','136'])).

thf('145',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v5_relat_1 @ X21 @ X23 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('153',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('157',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['134','156'])).

thf('158',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('159',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('161',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('164',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','108','118','119','162','163'])).

thf('165',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','164'])).

thf('166',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('168',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('169',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['167','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('173',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('174',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('175',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,
    ( ( v5_relat_1 @ sk_D @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v5_relat_1 @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['170','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v5_relat_1 @ sk_D @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('182',plain,
    ( ( v5_relat_1 @ sk_D @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('184',plain,
    ( ( v5_relat_1 @ sk_D @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
      | ~ ( v5_relat_1 @ X21 @ X23 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('196',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('197',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('200',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['203'])).

thf('205',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('206',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('208',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('210',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_B )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('212',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('215',plain,(
    ! [X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('217',plain,
    ( ( v1_relat_1 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('219',plain,
    ( ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k7_relat_1 @ sk_B @ sk_B )
      = sk_B ) ),
    inference(clc,[status(thm)],['210','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('223',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['221','224'])).

thf('226',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['220','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('231',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf('233',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('234',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('236',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['229','236'])).

thf('238',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('239',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['198','239'])).

thf('241',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('243',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_D )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
          = X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','108','118','119','162','163'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(simpl_trail,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['166','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('250',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('253',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('254',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['248','254'])).

thf('256',plain,(
    $false ),
    inference(demod,[status(thm)],['165','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ksqZns0y9l
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 30.52/30.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.52/30.71  % Solved by: fo/fo7.sh
% 30.52/30.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.52/30.71  % done 34162 iterations in 30.244s
% 30.52/30.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.52/30.71  % SZS output start Refutation
% 30.52/30.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.52/30.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 30.52/30.71  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 30.52/30.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 30.52/30.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 30.52/30.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.52/30.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.52/30.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.52/30.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.52/30.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.52/30.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 30.52/30.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 30.52/30.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.52/30.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.52/30.71  thf(sk_A_type, type, sk_A: $i).
% 30.52/30.71  thf(sk_D_type, type, sk_D: $i).
% 30.52/30.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.52/30.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 30.52/30.71  thf(sk_C_type, type, sk_C: $i).
% 30.52/30.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.52/30.71  thf(sk_B_type, type, sk_B: $i).
% 30.52/30.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.52/30.71  thf(t38_funct_2, conjecture,
% 30.52/30.71    (![A:$i,B:$i,C:$i,D:$i]:
% 30.52/30.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 30.52/30.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.52/30.71       ( ( r1_tarski @ C @ A ) =>
% 30.52/30.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 30.52/30.71           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 30.52/30.71             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 30.52/30.71             ( m1_subset_1 @
% 30.52/30.71               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 30.52/30.71               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 30.52/30.71  thf(zf_stmt_0, negated_conjecture,
% 30.52/30.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 30.52/30.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 30.52/30.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.52/30.71          ( ( r1_tarski @ C @ A ) =>
% 30.52/30.71            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 30.52/30.71              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 30.52/30.71                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 30.52/30.71                ( m1_subset_1 @
% 30.52/30.71                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 30.52/30.71                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 30.52/30.71    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 30.52/30.71  thf('0', plain,
% 30.52/30.71      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 30.52/30.71        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71             sk_B)
% 30.52/30.71        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('1', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('split', [status(esa)], ['0'])).
% 30.52/30.71  thf('2', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf(redefinition_k2_partfun1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i,D:$i]:
% 30.52/30.71     ( ( ( v1_funct_1 @ C ) & 
% 30.52/30.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.52/30.71       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 30.52/30.71  thf('3', plain,
% 30.52/30.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 30.52/30.71         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 30.52/30.71          | ~ (v1_funct_1 @ X45)
% 30.52/30.71          | ((k2_partfun1 @ X46 @ X47 @ X45 @ X48) = (k7_relat_1 @ X45 @ X48)))),
% 30.52/30.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 30.52/30.71  thf('4', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | ~ (v1_funct_1 @ sk_D))),
% 30.52/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.52/30.71  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('6', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['4', '5'])).
% 30.52/30.71  thf('7', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('demod', [status(thm)], ['1', '6'])).
% 30.52/30.71  thf('8', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf(dt_k2_partfun1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i,D:$i]:
% 30.52/30.71     ( ( ( v1_funct_1 @ C ) & 
% 30.52/30.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.52/30.71       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 30.52/30.71         ( m1_subset_1 @
% 30.52/30.71           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 30.52/30.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 30.52/30.71  thf('9', plain,
% 30.52/30.71      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 30.52/30.71         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 30.52/30.71          | ~ (v1_funct_1 @ X41)
% 30.52/30.71          | (v1_funct_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44)))),
% 30.52/30.71      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 30.52/30.71  thf('10', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 30.52/30.71          | ~ (v1_funct_1 @ sk_D))),
% 30.52/30.71      inference('sup-', [status(thm)], ['8', '9'])).
% 30.52/30.71  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('12', plain,
% 30.52/30.71      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['10', '11'])).
% 30.52/30.71  thf('13', plain,
% 30.52/30.71      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 30.52/30.71         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 30.52/30.71      inference('split', [status(esa)], ['0'])).
% 30.52/30.71  thf('14', plain,
% 30.52/30.71      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['12', '13'])).
% 30.52/30.71  thf(t60_relat_1, axiom,
% 30.52/30.71    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 30.52/30.71     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 30.52/30.71  thf('15', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 30.52/30.71  thf(t98_relat_1, axiom,
% 30.52/30.71    (![A:$i]:
% 30.52/30.71     ( ( v1_relat_1 @ A ) =>
% 30.52/30.71       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 30.52/30.71  thf('16', plain,
% 30.52/30.71      (![X20 : $i]:
% 30.52/30.71         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 30.52/30.71          | ~ (v1_relat_1 @ X20))),
% 30.52/30.71      inference('cnf', [status(esa)], [t98_relat_1])).
% 30.52/30.71  thf('17', plain,
% 30.52/30.71      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 30.52/30.71        | ~ (v1_relat_1 @ k1_xboole_0))),
% 30.52/30.71      inference('sup+', [status(thm)], ['15', '16'])).
% 30.52/30.71  thf(t4_subset_1, axiom,
% 30.52/30.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 30.52/30.71  thf('18', plain,
% 30.52/30.71      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 30.52/30.71  thf(cc1_relset_1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.52/30.71       ( v1_relat_1 @ C ) ))).
% 30.52/30.71  thf('19', plain,
% 30.52/30.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 30.52/30.71         ((v1_relat_1 @ X24)
% 30.52/30.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.52/30.71  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 30.52/30.71      inference('sup-', [status(thm)], ['18', '19'])).
% 30.52/30.71  thf('21', plain,
% 30.52/30.71      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['17', '20'])).
% 30.52/30.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 30.52/30.71  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf(t8_boole, axiom,
% 30.52/30.71    (![A:$i,B:$i]:
% 30.52/30.71     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 30.52/30.71  thf('23', plain,
% 30.52/30.71      (![X1 : $i, X2 : $i]:
% 30.52/30.71         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 30.52/30.71      inference('cnf', [status(esa)], [t8_boole])).
% 30.52/30.71  thf('24', plain,
% 30.52/30.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['22', '23'])).
% 30.52/30.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 30.52/30.71  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 30.52/30.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 30.52/30.71  thf('26', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup+', [status(thm)], ['24', '25'])).
% 30.52/30.71  thf(t102_relat_1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( v1_relat_1 @ C ) =>
% 30.52/30.71       ( ( r1_tarski @ A @ B ) =>
% 30.52/30.71         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 30.52/30.71  thf('27', plain,
% 30.52/30.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X15 @ X16)
% 30.52/30.71          | ~ (v1_relat_1 @ X17)
% 30.52/30.71          | ((k7_relat_1 @ (k7_relat_1 @ X17 @ X15) @ X16)
% 30.52/30.71              = (k7_relat_1 @ X17 @ X15)))),
% 30.52/30.71      inference('cnf', [status(esa)], [t102_relat_1])).
% 30.52/30.71  thf('28', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.52/30.71         (~ (v1_xboole_0 @ X1)
% 30.52/30.71          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 30.52/30.71              = (k7_relat_1 @ X2 @ X1))
% 30.52/30.71          | ~ (v1_relat_1 @ X2))),
% 30.52/30.71      inference('sup-', [status(thm)], ['26', '27'])).
% 30.52/30.71  thf('29', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 30.52/30.71            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 30.52/30.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 30.52/30.71          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 30.52/30.71      inference('sup+', [status(thm)], ['21', '28'])).
% 30.52/30.71  thf('30', plain,
% 30.52/30.71      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['17', '20'])).
% 30.52/30.71  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 30.52/30.71      inference('sup-', [status(thm)], ['18', '19'])).
% 30.52/30.71  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf('33', plain,
% 30.52/30.71      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 30.52/30.71  thf('34', plain,
% 30.52/30.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['22', '23'])).
% 30.52/30.71  thf('35', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('36', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('37', plain, ((r1_tarski @ sk_C @ sk_A)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('38', plain,
% 30.52/30.71      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['36', '37'])).
% 30.52/30.71  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 30.52/30.71  thf(t91_relat_1, axiom,
% 30.52/30.71    (![A:$i,B:$i]:
% 30.52/30.71     ( ( v1_relat_1 @ B ) =>
% 30.52/30.71       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 30.52/30.71         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 30.52/30.71  thf('40', plain,
% 30.52/30.71      (![X18 : $i, X19 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 30.52/30.71          | ~ (v1_relat_1 @ X19))),
% 30.52/30.71      inference('cnf', [status(esa)], [t91_relat_1])).
% 30.52/30.71  thf('41', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 30.52/30.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['39', '40'])).
% 30.52/30.71  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 30.52/30.71      inference('sup-', [status(thm)], ['18', '19'])).
% 30.52/30.71  thf('43', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 30.52/30.71      inference('demod', [status(thm)], ['41', '42'])).
% 30.52/30.71  thf('44', plain,
% 30.52/30.71      ((((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C)) = (sk_C)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['38', '43'])).
% 30.52/30.71  thf('45', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (((k1_relat_1 @ (k7_relat_1 @ X0 @ sk_C)) = (sk_C))
% 30.52/30.71           | ~ (v1_xboole_0 @ X0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['34', '44'])).
% 30.52/30.71  thf('46', plain,
% 30.52/30.71      (((((k1_relat_1 @ k1_xboole_0) = (sk_C)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['33', '45'])).
% 30.52/30.71  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 30.52/30.71  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf('49', plain,
% 30.52/30.71      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['46', '47', '48'])).
% 30.52/30.71  thf('50', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['4', '5'])).
% 30.52/30.71  thf('51', plain,
% 30.52/30.71      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 30.52/30.71         <= (~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)))),
% 30.52/30.71      inference('split', [status(esa)], ['0'])).
% 30.52/30.71  thf('52', plain,
% 30.52/30.71      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 30.52/30.71         <= (~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['50', '51'])).
% 30.52/30.71  thf('53', plain,
% 30.52/30.71      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ k1_xboole_0 @ sk_B))
% 30.52/30.71         <= (~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)) & 
% 30.52/30.71             (((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['49', '52'])).
% 30.52/30.71  thf('54', plain,
% 30.52/30.71      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['46', '47', '48'])).
% 30.52/30.71  thf('55', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('57', plain,
% 30.52/30.71      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['55', '56'])).
% 30.52/30.71  thf(d1_funct_2, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.52/30.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.52/30.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 30.52/30.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 30.52/30.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.52/30.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 30.52/30.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 30.52/30.71  thf(zf_stmt_1, axiom,
% 30.52/30.71    (![C:$i,B:$i,A:$i]:
% 30.52/30.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 30.52/30.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 30.52/30.71  thf('58', plain,
% 30.52/30.71      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.52/30.71         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 30.52/30.71          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 30.52/30.71          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.52/30.71  thf('59', plain,
% 30.52/30.71      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 30.52/30.71         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['57', '58'])).
% 30.52/30.71  thf('60', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('61', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf(redefinition_k1_relset_1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.52/30.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 30.52/30.71  thf('62', plain,
% 30.52/30.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 30.52/30.71         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 30.52/30.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 30.52/30.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.52/30.71  thf('63', plain,
% 30.52/30.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 30.52/30.71      inference('sup-', [status(thm)], ['61', '62'])).
% 30.52/30.71  thf('64', plain,
% 30.52/30.71      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['60', '63'])).
% 30.52/30.71  thf('65', plain,
% 30.52/30.71      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 30.52/30.71         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['59', '64'])).
% 30.52/30.71  thf('66', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('67', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 30.52/30.71  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 30.52/30.71  thf(zf_stmt_4, axiom,
% 30.52/30.71    (![B:$i,A:$i]:
% 30.52/30.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.52/30.71       ( zip_tseitin_0 @ B @ A ) ))).
% 30.52/30.71  thf(zf_stmt_5, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.52/30.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 30.52/30.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.52/30.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 30.52/30.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 30.52/30.71  thf('68', plain,
% 30.52/30.71      (![X38 : $i, X39 : $i, X40 : $i]:
% 30.52/30.71         (~ (zip_tseitin_0 @ X38 @ X39)
% 30.52/30.71          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 30.52/30.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.52/30.71  thf('69', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('70', plain,
% 30.52/30.71      (((~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)
% 30.52/30.71         | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['66', '69'])).
% 30.52/30.71  thf('71', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('72', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 30.52/30.71      inference('simplify', [status(thm)], ['71'])).
% 30.52/30.71  thf('73', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('74', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['70', '72', '73'])).
% 30.52/30.71  thf('75', plain,
% 30.52/30.71      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['65', '74'])).
% 30.52/30.71  thf('76', plain,
% 30.52/30.71      (![X20 : $i]:
% 30.52/30.71         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 30.52/30.71          | ~ (v1_relat_1 @ X20))),
% 30.52/30.71      inference('cnf', [status(esa)], [t98_relat_1])).
% 30.52/30.71  thf('77', plain,
% 30.52/30.71      (((((k7_relat_1 @ sk_D @ k1_xboole_0) = (sk_D)) | ~ (v1_relat_1 @ sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['75', '76'])).
% 30.52/30.71  thf('78', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('79', plain,
% 30.52/30.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 30.52/30.71         ((v1_relat_1 @ X24)
% 30.52/30.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.52/30.71  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('81', plain,
% 30.52/30.71      ((((k7_relat_1 @ sk_D @ k1_xboole_0) = (sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['77', '80'])).
% 30.52/30.71  thf('82', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.52/30.71         (~ (v1_xboole_0 @ X1)
% 30.52/30.71          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 30.52/30.71              = (k7_relat_1 @ X2 @ X1))
% 30.52/30.71          | ~ (v1_relat_1 @ X2))),
% 30.52/30.71      inference('sup-', [status(thm)], ['26', '27'])).
% 30.52/30.71  thf('83', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (((k7_relat_1 @ sk_D @ X0) = (k7_relat_1 @ sk_D @ k1_xboole_0))
% 30.52/30.71           | ~ (v1_relat_1 @ sk_D)
% 30.52/30.71           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['81', '82'])).
% 30.52/30.71  thf('84', plain,
% 30.52/30.71      ((((k7_relat_1 @ sk_D @ k1_xboole_0) = (sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['77', '80'])).
% 30.52/30.71  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf('87', plain,
% 30.52/30.71      ((![X0 : $i]: ((k7_relat_1 @ sk_D @ X0) = (sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 30.52/30.71  thf('88', plain,
% 30.52/30.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('89', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('90', plain,
% 30.52/30.71      (((m1_subset_1 @ sk_D @ 
% 30.52/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup+', [status(thm)], ['88', '89'])).
% 30.52/30.71  thf(t113_zfmisc_1, axiom,
% 30.52/30.71    (![A:$i,B:$i]:
% 30.52/30.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 30.52/30.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 30.52/30.71  thf('91', plain,
% 30.52/30.71      (![X4 : $i, X5 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 30.52/30.71  thf('92', plain,
% 30.52/30.71      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['91'])).
% 30.52/30.71  thf('93', plain,
% 30.52/30.71      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['90', '92'])).
% 30.52/30.71  thf('94', plain,
% 30.52/30.71      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['91'])).
% 30.52/30.71  thf(cc2_relset_1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.52/30.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 30.52/30.71  thf('95', plain,
% 30.52/30.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.52/30.71         ((v5_relat_1 @ X27 @ X29)
% 30.52/30.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 30.52/30.71  thf('96', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]:
% 30.52/30.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 30.52/30.71          | (v5_relat_1 @ X1 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['94', '95'])).
% 30.52/30.71  thf('97', plain,
% 30.52/30.71      ((![X0 : $i]: (v5_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['93', '96'])).
% 30.52/30.71  thf(d19_relat_1, axiom,
% 30.52/30.71    (![A:$i,B:$i]:
% 30.52/30.71     ( ( v1_relat_1 @ B ) =>
% 30.52/30.71       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 30.52/30.71  thf('98', plain,
% 30.52/30.71      (![X13 : $i, X14 : $i]:
% 30.52/30.71         (~ (v5_relat_1 @ X13 @ X14)
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 30.52/30.71          | ~ (v1_relat_1 @ X13))),
% 30.52/30.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 30.52/30.71  thf('99', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['97', '98'])).
% 30.52/30.71  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('101', plain,
% 30.52/30.71      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['99', '100'])).
% 30.52/30.71  thf(t4_funct_2, axiom,
% 30.52/30.71    (![A:$i,B:$i]:
% 30.52/30.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 30.52/30.71       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 30.52/30.71         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 30.52/30.71           ( m1_subset_1 @
% 30.52/30.71             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 30.52/30.71  thf('102', plain,
% 30.52/30.71      (![X49 : $i, X50 : $i]:
% 30.52/30.71         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 30.52/30.71          | (v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ X50)
% 30.52/30.71          | ~ (v1_funct_1 @ X49)
% 30.52/30.71          | ~ (v1_relat_1 @ X49))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_funct_2])).
% 30.52/30.71  thf('103', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (~ (v1_relat_1 @ sk_D)
% 30.52/30.71           | ~ (v1_funct_1 @ sk_D)
% 30.52/30.71           | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ X0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['101', '102'])).
% 30.52/30.71  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('106', plain,
% 30.52/30.71      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['65', '74'])).
% 30.52/30.71  thf('107', plain,
% 30.52/30.71      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 30.52/30.71  thf('108', plain,
% 30.52/30.71      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 30.52/30.71       ~ (((sk_A) = (k1_xboole_0)))),
% 30.52/30.71      inference('demod', [status(thm)], ['53', '54', '87', '107'])).
% 30.52/30.71  thf('109', plain,
% 30.52/30.71      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['46', '47', '48'])).
% 30.52/30.71  thf('110', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['4', '5'])).
% 30.52/30.71  thf('111', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('split', [status(esa)], ['0'])).
% 30.52/30.71  thf('112', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['110', '111'])).
% 30.52/30.71  thf('113', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 30.52/30.71             (((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['109', '112'])).
% 30.52/30.71  thf('114', plain,
% 30.52/30.71      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['46', '47', '48'])).
% 30.52/30.71  thf('115', plain,
% 30.52/30.71      ((![X0 : $i]: ((k7_relat_1 @ sk_D @ X0) = (sk_D)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 30.52/30.71  thf('116', plain,
% 30.52/30.71      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['91'])).
% 30.52/30.71  thf('117', plain,
% 30.52/30.71      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 30.52/30.71         <= ((((sk_A) = (k1_xboole_0))))),
% 30.52/30.71      inference('demod', [status(thm)], ['90', '92'])).
% 30.52/30.71  thf('118', plain,
% 30.52/30.71      (~ (((sk_A) = (k1_xboole_0))) | 
% 30.52/30.71       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 30.52/30.71      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 30.52/30.71  thf('119', plain,
% 30.52/30.71      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('120', plain, ((r1_tarski @ sk_C @ sk_A)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('121', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('122', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('123', plain,
% 30.52/30.71      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['121', '122'])).
% 30.52/30.71  thf('124', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('125', plain,
% 30.52/30.71      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.52/30.71         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 30.52/30.71          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 30.52/30.71          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.52/30.71  thf('126', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 30.52/30.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['124', '125'])).
% 30.52/30.71  thf('127', plain,
% 30.52/30.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 30.52/30.71      inference('sup-', [status(thm)], ['61', '62'])).
% 30.52/30.71  thf('128', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('demod', [status(thm)], ['126', '127'])).
% 30.52/30.71  thf('129', plain,
% 30.52/30.71      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['123', '128'])).
% 30.52/30.71  thf('130', plain,
% 30.52/30.71      (![X18 : $i, X19 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 30.52/30.71          | ~ (v1_relat_1 @ X19))),
% 30.52/30.71      inference('cnf', [status(esa)], [t91_relat_1])).
% 30.52/30.71  thf('131', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X0 @ sk_A)
% 30.52/30.71          | ((sk_B) = (k1_xboole_0))
% 30.52/30.71          | ~ (v1_relat_1 @ sk_D)
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['129', '130'])).
% 30.52/30.71  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('133', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X0 @ sk_A)
% 30.52/30.71          | ((sk_B) = (k1_xboole_0))
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 30.52/30.71      inference('demod', [status(thm)], ['131', '132'])).
% 30.52/30.71  thf('134', plain,
% 30.52/30.71      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))
% 30.52/30.71        | ((sk_B) = (k1_xboole_0)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['120', '133'])).
% 30.52/30.71  thf('135', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('136', plain,
% 30.52/30.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.52/30.71         ((v5_relat_1 @ X27 @ X29)
% 30.52/30.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 30.52/30.71  thf('137', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 30.52/30.71      inference('sup-', [status(thm)], ['135', '136'])).
% 30.52/30.71  thf(fc22_relat_1, axiom,
% 30.52/30.71    (![A:$i,B:$i,C:$i]:
% 30.52/30.71     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) ) =>
% 30.52/30.71       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 30.52/30.71         ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 30.52/30.71  thf('138', plain,
% 30.52/30.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 30.52/30.71         ((v5_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 30.52/30.71          | ~ (v5_relat_1 @ X21 @ X23)
% 30.52/30.71          | ~ (v1_relat_1 @ X21))),
% 30.52/30.71      inference('cnf', [status(esa)], [fc22_relat_1])).
% 30.52/30.71  thf('139', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_relat_1 @ sk_D)
% 30.52/30.71          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B))),
% 30.52/30.71      inference('sup-', [status(thm)], ['137', '138'])).
% 30.52/30.71  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('141', plain,
% 30.52/30.71      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 30.52/30.71      inference('demod', [status(thm)], ['139', '140'])).
% 30.52/30.71  thf('142', plain,
% 30.52/30.71      (![X13 : $i, X14 : $i]:
% 30.52/30.71         (~ (v5_relat_1 @ X13 @ X14)
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 30.52/30.71          | ~ (v1_relat_1 @ X13))),
% 30.52/30.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 30.52/30.71  thf('143', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 30.52/30.71      inference('sup-', [status(thm)], ['141', '142'])).
% 30.52/30.71  thf('144', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 30.52/30.71      inference('sup-', [status(thm)], ['135', '136'])).
% 30.52/30.71  thf('145', plain,
% 30.52/30.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 30.52/30.71         ((v1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 30.52/30.71          | ~ (v5_relat_1 @ X21 @ X23)
% 30.52/30.71          | ~ (v1_relat_1 @ X21))),
% 30.52/30.71      inference('cnf', [status(esa)], [fc22_relat_1])).
% 30.52/30.71  thf('146', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['144', '145'])).
% 30.52/30.71  thf('147', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('148', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['146', '147'])).
% 30.52/30.71  thf('149', plain,
% 30.52/30.71      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 30.52/30.71      inference('demod', [status(thm)], ['143', '148'])).
% 30.52/30.71  thf('150', plain,
% 30.52/30.71      (![X49 : $i, X50 : $i]:
% 30.52/30.71         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 30.52/30.71          | (v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ X50)
% 30.52/30.71          | ~ (v1_funct_1 @ X49)
% 30.52/30.71          | ~ (v1_relat_1 @ X49))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_funct_2])).
% 30.52/30.71  thf('151', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 30.52/30.71      inference('sup-', [status(thm)], ['149', '150'])).
% 30.52/30.71  thf('152', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['146', '147'])).
% 30.52/30.71  thf('153', plain,
% 30.52/30.71      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['10', '11'])).
% 30.52/30.71  thf('154', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['4', '5'])).
% 30.52/30.71  thf('155', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['153', '154'])).
% 30.52/30.71  thf('156', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 30.52/30.71      inference('demod', [status(thm)], ['151', '152', '155'])).
% 30.52/30.71  thf('157', plain,
% 30.52/30.71      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 30.52/30.71        | ((sk_B) = (k1_xboole_0)))),
% 30.52/30.71      inference('sup+', [status(thm)], ['134', '156'])).
% 30.52/30.71  thf('158', plain,
% 30.52/30.71      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 30.52/30.71         <= (~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['50', '51'])).
% 30.52/30.71  thf('159', plain,
% 30.52/30.71      ((((sk_B) = (k1_xboole_0)))
% 30.52/30.71         <= (~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['157', '158'])).
% 30.52/30.71  thf('160', plain,
% 30.52/30.71      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 30.52/30.71      inference('split', [status(esa)], ['35'])).
% 30.52/30.71  thf('161', plain,
% 30.52/30.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 30.52/30.71         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 30.52/30.71             ~
% 30.52/30.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 30.52/30.71               sk_B)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['159', '160'])).
% 30.52/30.71  thf('162', plain,
% 30.52/30.71      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 30.52/30.71       (((sk_B) = (k1_xboole_0)))),
% 30.52/30.71      inference('simplify', [status(thm)], ['161'])).
% 30.52/30.71  thf('163', plain,
% 30.52/30.71      (~
% 30.52/30.71       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 30.52/30.71       ~
% 30.52/30.71       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 30.52/30.71       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 30.52/30.71      inference('split', [status(esa)], ['0'])).
% 30.52/30.71  thf('164', plain,
% 30.52/30.71      (~
% 30.52/30.71       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 30.52/30.71      inference('sat_resolution*', [status(thm)],
% 30.52/30.71                ['14', '108', '118', '119', '162', '163'])).
% 30.52/30.71  thf('165', plain,
% 30.52/30.71      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 30.52/30.71      inference('simpl_trail', [status(thm)], ['7', '164'])).
% 30.52/30.71  thf('166', plain, ((r1_tarski @ sk_C @ sk_A)),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('167', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('168', plain,
% 30.52/30.71      (![X4 : $i, X5 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 30.52/30.71  thf('169', plain,
% 30.52/30.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['168'])).
% 30.52/30.71  thf('170', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 30.52/30.71      inference('sup+', [status(thm)], ['167', '169'])).
% 30.52/30.71  thf('171', plain,
% 30.52/30.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.52/30.71  thf('172', plain,
% 30.52/30.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['22', '23'])).
% 30.52/30.71  thf('173', plain,
% 30.52/30.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['168'])).
% 30.52/30.71  thf('174', plain,
% 30.52/30.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.52/30.71         ((v5_relat_1 @ X27 @ X29)
% 30.52/30.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 30.52/30.71  thf('175', plain,
% 30.52/30.71      (![X1 : $i]:
% 30.52/30.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 30.52/30.71          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['173', '174'])).
% 30.52/30.71  thf('176', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]:
% 30.52/30.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 30.52/30.71          | ~ (v1_xboole_0 @ X0)
% 30.52/30.71          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['172', '175'])).
% 30.52/30.71  thf('177', plain,
% 30.52/30.71      (((v5_relat_1 @ sk_D @ k1_xboole_0)
% 30.52/30.71        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['171', '176'])).
% 30.52/30.71  thf('178', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 30.52/30.71          | (zip_tseitin_0 @ sk_B @ X0)
% 30.52/30.71          | (v5_relat_1 @ sk_D @ k1_xboole_0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['170', '177'])).
% 30.52/30.71  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf('180', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ sk_B @ X0) | (v5_relat_1 @ sk_D @ k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['178', '179'])).
% 30.52/30.71  thf('181', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('182', plain,
% 30.52/30.71      (((v5_relat_1 @ sk_D @ k1_xboole_0)
% 30.52/30.71        | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['180', '181'])).
% 30.52/30.71  thf('183', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('demod', [status(thm)], ['126', '127'])).
% 30.52/30.71  thf('184', plain,
% 30.52/30.71      (((v5_relat_1 @ sk_D @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['182', '183'])).
% 30.52/30.71  thf('185', plain,
% 30.52/30.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 30.52/30.71         ((v5_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 30.52/30.71          | ~ (v5_relat_1 @ X21 @ X23)
% 30.52/30.71          | ~ (v1_relat_1 @ X21))),
% 30.52/30.71      inference('cnf', [status(esa)], [fc22_relat_1])).
% 30.52/30.71  thf('186', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | ~ (v1_relat_1 @ sk_D)
% 30.52/30.71          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['184', '185'])).
% 30.52/30.71  thf('187', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('188', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['186', '187'])).
% 30.52/30.71  thf('189', plain,
% 30.52/30.71      (![X13 : $i, X14 : $i]:
% 30.52/30.71         (~ (v5_relat_1 @ X13 @ X14)
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 30.52/30.71          | ~ (v1_relat_1 @ X13))),
% 30.52/30.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 30.52/30.71  thf('190', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ k1_xboole_0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['188', '189'])).
% 30.52/30.71  thf('191', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['146', '147'])).
% 30.52/30.71  thf('192', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['190', '191'])).
% 30.52/30.71  thf('193', plain,
% 30.52/30.71      (![X49 : $i, X50 : $i]:
% 30.52/30.71         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 30.52/30.71          | (m1_subset_1 @ X49 @ 
% 30.52/30.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ X50)))
% 30.52/30.71          | ~ (v1_funct_1 @ X49)
% 30.52/30.71          | ~ (v1_relat_1 @ X49))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_funct_2])).
% 30.52/30.71  thf('194', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71             (k1_zfmisc_1 @ 
% 30.52/30.71              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 30.52/30.71               k1_xboole_0))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['192', '193'])).
% 30.52/30.71  thf('195', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['146', '147'])).
% 30.52/30.71  thf('196', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['153', '154'])).
% 30.52/30.71  thf('197', plain,
% 30.52/30.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['168'])).
% 30.52/30.71  thf('198', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71             (k1_zfmisc_1 @ k1_xboole_0)))),
% 30.52/30.71      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 30.52/30.71  thf('199', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('200', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 30.52/30.71  thf('201', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]:
% 30.52/30.71         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 30.52/30.71      inference('sup+', [status(thm)], ['199', '200'])).
% 30.52/30.71  thf('202', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('203', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 30.52/30.71         (((X1) = (k1_relat_1 @ X0))
% 30.52/30.71          | (zip_tseitin_0 @ X0 @ X3)
% 30.52/30.71          | (zip_tseitin_0 @ X1 @ X2))),
% 30.52/30.71      inference('sup+', [status(thm)], ['201', '202'])).
% 30.52/30.71  thf('204', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X1 @ X0) | ((X1) = (k1_relat_1 @ X1)))),
% 30.52/30.71      inference('eq_fact', [status(thm)], ['203'])).
% 30.52/30.71  thf('205', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('206', plain,
% 30.52/30.71      ((((sk_B) = (k1_relat_1 @ sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['204', '205'])).
% 30.52/30.71  thf('207', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('demod', [status(thm)], ['126', '127'])).
% 30.52/30.71  thf('208', plain,
% 30.52/30.71      ((((sk_B) = (k1_relat_1 @ sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['206', '207'])).
% 30.52/30.71  thf('209', plain,
% 30.52/30.71      (![X20 : $i]:
% 30.52/30.71         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 30.52/30.71          | ~ (v1_relat_1 @ X20))),
% 30.52/30.71      inference('cnf', [status(esa)], [t98_relat_1])).
% 30.52/30.71  thf('210', plain,
% 30.52/30.71      ((((k7_relat_1 @ sk_B @ sk_B) = (sk_B))
% 30.52/30.71        | ((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71        | ~ (v1_relat_1 @ sk_B))),
% 30.52/30.71      inference('sup+', [status(thm)], ['208', '209'])).
% 30.52/30.71  thf('211', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('212', plain,
% 30.52/30.71      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 30.52/30.71  thf('213', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.52/30.71         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 30.52/30.71      inference('sup+', [status(thm)], ['211', '212'])).
% 30.52/30.71  thf('214', plain,
% 30.52/30.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 30.52/30.71         ((v1_relat_1 @ X24)
% 30.52/30.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 30.52/30.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.52/30.71  thf('215', plain,
% 30.52/30.71      (![X2 : $i, X3 : $i]: ((zip_tseitin_0 @ X2 @ X3) | (v1_relat_1 @ X2))),
% 30.52/30.71      inference('sup-', [status(thm)], ['213', '214'])).
% 30.52/30.71  thf('216', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('217', plain,
% 30.52/30.71      (((v1_relat_1 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['215', '216'])).
% 30.52/30.71  thf('218', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('demod', [status(thm)], ['126', '127'])).
% 30.52/30.71  thf('219', plain, (((v1_relat_1 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['217', '218'])).
% 30.52/30.71  thf('220', plain,
% 30.52/30.71      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k7_relat_1 @ sk_B @ sk_B) = (sk_B)))),
% 30.52/30.71      inference('clc', [status(thm)], ['210', '219'])).
% 30.52/30.71  thf('221', plain,
% 30.52/30.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['22', '23'])).
% 30.52/30.71  thf('222', plain,
% 30.52/30.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup-', [status(thm)], ['22', '23'])).
% 30.52/30.71  thf('223', plain,
% 30.52/30.71      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('demod', [status(thm)], ['17', '20'])).
% 30.52/30.71  thf('224', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 30.52/30.71          | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup+', [status(thm)], ['222', '223'])).
% 30.52/30.71  thf('225', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]:
% 30.52/30.71         (((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 30.52/30.71          | ~ (v1_xboole_0 @ X0)
% 30.52/30.71          | ~ (v1_xboole_0 @ X1))),
% 30.52/30.71      inference('sup+', [status(thm)], ['221', '224'])).
% 30.52/30.71  thf('226', plain,
% 30.52/30.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 30.52/30.71      inference('simplify', [status(thm)], ['168'])).
% 30.52/30.71  thf('227', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X2 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 30.52/30.71          | ~ (v1_xboole_0 @ X1)
% 30.52/30.71          | ~ (v1_xboole_0 @ X0))),
% 30.52/30.71      inference('sup+', [status(thm)], ['225', '226'])).
% 30.52/30.71  thf('228', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 30.52/30.71          | ((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | ~ (v1_xboole_0 @ sk_B)
% 30.52/30.71          | ~ (v1_xboole_0 @ sk_B))),
% 30.52/30.71      inference('sup+', [status(thm)], ['220', '227'])).
% 30.52/30.71  thf('229', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_xboole_0 @ sk_B)
% 30.52/30.71          | ((sk_A) = (k1_relat_1 @ sk_D))
% 30.52/30.71          | ((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0)))),
% 30.52/30.71      inference('simplify', [status(thm)], ['228'])).
% 30.52/30.71  thf('230', plain,
% 30.52/30.71      (![X33 : $i, X34 : $i]:
% 30.52/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.52/30.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.52/30.71  thf('231', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.52/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.52/30.71  thf('232', plain,
% 30.52/30.71      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 30.52/30.71      inference('sup+', [status(thm)], ['230', '231'])).
% 30.52/30.71  thf('233', plain,
% 30.52/30.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['67', '68'])).
% 30.52/30.71  thf('234', plain,
% 30.52/30.71      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 30.52/30.71      inference('sup-', [status(thm)], ['232', '233'])).
% 30.52/30.71  thf('235', plain,
% 30.52/30.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('demod', [status(thm)], ['126', '127'])).
% 30.52/30.71  thf('236', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('sup-', [status(thm)], ['234', '235'])).
% 30.52/30.71  thf('237', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 30.52/30.71          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 30.52/30.71      inference('clc', [status(thm)], ['229', '236'])).
% 30.52/30.71  thf('238', plain,
% 30.52/30.71      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['110', '111'])).
% 30.52/30.71  thf('239', plain,
% 30.52/30.71      (((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71            (k1_zfmisc_1 @ k1_xboole_0))
% 30.52/30.71         | ((sk_A) = (k1_relat_1 @ sk_D))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['237', '238'])).
% 30.52/30.71  thf('240', plain,
% 30.52/30.71      (((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['198', '239'])).
% 30.52/30.71  thf('241', plain,
% 30.52/30.71      ((((sk_A) = (k1_relat_1 @ sk_D)))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('simplify', [status(thm)], ['240'])).
% 30.52/30.71  thf('242', plain,
% 30.52/30.71      (![X18 : $i, X19 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 30.52/30.71          | ~ (v1_relat_1 @ X19))),
% 30.52/30.71      inference('cnf', [status(esa)], [t91_relat_1])).
% 30.52/30.71  thf('243', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (~ (r1_tarski @ X0 @ sk_A)
% 30.52/30.71           | ~ (v1_relat_1 @ sk_D)
% 30.52/30.71           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['241', '242'])).
% 30.52/30.71  thf('244', plain, ((v1_relat_1 @ sk_D)),
% 30.52/30.71      inference('sup-', [status(thm)], ['78', '79'])).
% 30.52/30.71  thf('245', plain,
% 30.52/30.71      ((![X0 : $i]:
% 30.52/30.71          (~ (r1_tarski @ X0 @ sk_A)
% 30.52/30.71           | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))))
% 30.52/30.71         <= (~
% 30.52/30.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 30.52/30.71      inference('demod', [status(thm)], ['243', '244'])).
% 30.52/30.71  thf('246', plain,
% 30.52/30.71      (~
% 30.52/30.71       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 30.52/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 30.52/30.71      inference('sat_resolution*', [status(thm)],
% 30.52/30.71                ['14', '108', '118', '119', '162', '163'])).
% 30.52/30.71  thf('247', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (r1_tarski @ X0 @ sk_A)
% 30.52/30.71          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 30.52/30.71      inference('simpl_trail', [status(thm)], ['245', '246'])).
% 30.52/30.71  thf('248', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 30.52/30.71      inference('sup-', [status(thm)], ['166', '247'])).
% 30.52/30.71  thf('249', plain,
% 30.52/30.71      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 30.52/30.71      inference('demod', [status(thm)], ['143', '148'])).
% 30.52/30.71  thf('250', plain,
% 30.52/30.71      (![X49 : $i, X50 : $i]:
% 30.52/30.71         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 30.52/30.71          | (m1_subset_1 @ X49 @ 
% 30.52/30.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ X50)))
% 30.52/30.71          | ~ (v1_funct_1 @ X49)
% 30.52/30.71          | ~ (v1_relat_1 @ X49))),
% 30.52/30.71      inference('cnf', [status(esa)], [t4_funct_2])).
% 30.52/30.71  thf('251', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 30.52/30.71          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71             (k1_zfmisc_1 @ 
% 30.52/30.71              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 30.52/30.71      inference('sup-', [status(thm)], ['249', '250'])).
% 30.52/30.71  thf('252', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['146', '147'])).
% 30.52/30.71  thf('253', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 30.52/30.71      inference('demod', [status(thm)], ['153', '154'])).
% 30.52/30.71  thf('254', plain,
% 30.52/30.71      (![X0 : $i]:
% 30.52/30.71         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 30.52/30.71          (k1_zfmisc_1 @ 
% 30.52/30.71           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 30.52/30.71      inference('demod', [status(thm)], ['251', '252', '253'])).
% 30.52/30.71  thf('255', plain,
% 30.52/30.71      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 30.52/30.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 30.52/30.71      inference('sup+', [status(thm)], ['248', '254'])).
% 30.52/30.71  thf('256', plain, ($false), inference('demod', [status(thm)], ['165', '255'])).
% 30.52/30.71  
% 30.52/30.71  % SZS output end Refutation
% 30.52/30.71  
% 30.52/30.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
