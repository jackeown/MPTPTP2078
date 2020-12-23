%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M41kTxflvv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:13 EST 2020

% Result     : Theorem 33.42s
% Output     : Refutation 33.45s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 489 expanded)
%              Number of leaves         :   48 ( 167 expanded)
%              Depth                    :   19
%              Number of atoms          : 1553 (10159 expanded)
%              Number of equality atoms :   61 ( 108 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_funct_2 @ X48 @ X47 )
        = ( k2_funct_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) )
      | ~ ( v3_funct_2 @ X47 @ X48 @ X48 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X48 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('40',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','37','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('47',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','36'])).

thf('58',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('64',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
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

thf('70',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['78'])).

thf('80',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['71','80','83'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('85',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('86',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('94',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','84','90','91','92','93'])).

thf('95',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('96',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('100',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','106'])).

thf('108',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('111',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('112',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['108','109','110','111','112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M41kTxflvv
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 33.42/33.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 33.42/33.62  % Solved by: fo/fo7.sh
% 33.42/33.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.42/33.62  % done 10527 iterations in 33.154s
% 33.42/33.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 33.42/33.62  % SZS output start Refutation
% 33.42/33.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 33.42/33.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 33.42/33.62  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 33.42/33.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 33.42/33.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 33.42/33.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 33.42/33.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 33.42/33.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 33.42/33.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 33.42/33.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 33.42/33.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 33.42/33.62  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 33.42/33.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 33.42/33.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 33.42/33.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 33.42/33.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 33.42/33.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 33.42/33.62  thf(sk_B_type, type, sk_B: $i).
% 33.42/33.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 33.42/33.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.42/33.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 33.42/33.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 33.42/33.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 33.42/33.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 33.42/33.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 33.42/33.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 33.42/33.62  thf(sk_A_type, type, sk_A: $i).
% 33.42/33.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 33.42/33.62  thf(t61_funct_1, axiom,
% 33.42/33.62    (![A:$i]:
% 33.42/33.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.42/33.62       ( ( v2_funct_1 @ A ) =>
% 33.42/33.62         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 33.42/33.62             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 33.42/33.62           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 33.42/33.62             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 33.42/33.62  thf('0', plain,
% 33.42/33.62      (![X9 : $i]:
% 33.42/33.62         (~ (v2_funct_1 @ X9)
% 33.42/33.62          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 33.42/33.62              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 33.42/33.62          | ~ (v1_funct_1 @ X9)
% 33.42/33.62          | ~ (v1_relat_1 @ X9))),
% 33.42/33.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 33.42/33.62  thf(t88_funct_2, conjecture,
% 33.42/33.62    (![A:$i,B:$i]:
% 33.42/33.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 33.42/33.62         ( v3_funct_2 @ B @ A @ A ) & 
% 33.42/33.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 33.42/33.62       ( ( r2_relset_1 @
% 33.42/33.62           A @ A @ 
% 33.42/33.62           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 33.42/33.62           ( k6_partfun1 @ A ) ) & 
% 33.42/33.62         ( r2_relset_1 @
% 33.42/33.62           A @ A @ 
% 33.42/33.62           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 33.42/33.62           ( k6_partfun1 @ A ) ) ) ))).
% 33.42/33.62  thf(zf_stmt_0, negated_conjecture,
% 33.42/33.62    (~( ![A:$i,B:$i]:
% 33.42/33.62        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 33.42/33.62            ( v3_funct_2 @ B @ A @ A ) & 
% 33.42/33.62            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 33.42/33.62          ( ( r2_relset_1 @
% 33.42/33.62              A @ A @ 
% 33.42/33.62              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 33.42/33.62              ( k6_partfun1 @ A ) ) & 
% 33.42/33.62            ( r2_relset_1 @
% 33.42/33.62              A @ A @ 
% 33.42/33.62              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 33.42/33.62              ( k6_partfun1 @ A ) ) ) ) )),
% 33.42/33.62    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 33.42/33.62  thf('1', plain,
% 33.42/33.62      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.62           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.42/33.62            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.42/33.62           (k6_partfun1 @ sk_A))
% 33.42/33.62        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.62             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.62              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.62             (k6_partfun1 @ sk_A)))),
% 33.42/33.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.62  thf('2', plain,
% 33.42/33.62      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.62           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.62            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.63           (k6_partfun1 @ sk_A)))
% 33.42/33.63         <= (~
% 33.42/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.63               (k6_partfun1 @ sk_A))))),
% 33.42/33.63      inference('split', [status(esa)], ['1'])).
% 33.42/33.63  thf(redefinition_k6_partfun1, axiom,
% 33.42/33.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 33.42/33.63  thf('3', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 33.42/33.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.42/33.63  thf('4', plain,
% 33.42/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.63            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.63           (k6_relat_1 @ sk_A)))
% 33.42/33.63         <= (~
% 33.42/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.63               (k6_partfun1 @ sk_A))))),
% 33.42/33.63      inference('demod', [status(thm)], ['2', '3'])).
% 33.42/33.63  thf('5', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(redefinition_k2_funct_2, axiom,
% 33.42/33.63    (![A:$i,B:$i]:
% 33.42/33.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 33.42/33.63         ( v3_funct_2 @ B @ A @ A ) & 
% 33.42/33.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 33.42/33.63       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 33.42/33.63  thf('6', plain,
% 33.42/33.63      (![X47 : $i, X48 : $i]:
% 33.42/33.63         (((k2_funct_2 @ X48 @ X47) = (k2_funct_1 @ X47))
% 33.42/33.63          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))
% 33.42/33.63          | ~ (v3_funct_2 @ X47 @ X48 @ X48)
% 33.42/33.63          | ~ (v1_funct_2 @ X47 @ X48 @ X48)
% 33.42/33.63          | ~ (v1_funct_1 @ X47))),
% 33.42/33.63      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 33.42/33.63  thf('7', plain,
% 33.42/33.63      ((~ (v1_funct_1 @ sk_B)
% 33.42/33.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 33.42/33.63      inference('sup-', [status(thm)], ['5', '6'])).
% 33.42/33.63  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 33.42/33.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 33.42/33.63  thf('12', plain,
% 33.42/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 33.42/33.63            sk_B) @ 
% 33.42/33.63           (k6_relat_1 @ sk_A)))
% 33.42/33.63         <= (~
% 33.42/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.42/33.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.42/33.63               (k6_partfun1 @ sk_A))))),
% 33.42/33.63      inference('demod', [status(thm)], ['4', '11'])).
% 33.42/33.63  thf('13', plain,
% 33.42/33.63      (![X9 : $i]:
% 33.42/33.63         (~ (v2_funct_1 @ X9)
% 33.42/33.63          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 33.42/33.63              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 33.42/33.63          | ~ (v1_funct_1 @ X9)
% 33.42/33.63          | ~ (v1_relat_1 @ X9))),
% 33.42/33.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 33.42/33.63  thf('14', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(t31_funct_2, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i]:
% 33.42/33.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 33.42/33.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.42/33.63       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 33.42/33.63         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 33.42/33.63           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 33.42/33.63           ( m1_subset_1 @
% 33.42/33.63             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 33.42/33.63  thf('15', plain,
% 33.42/33.63      (![X50 : $i, X51 : $i, X52 : $i]:
% 33.42/33.63         (~ (v2_funct_1 @ X50)
% 33.42/33.63          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 33.42/33.63          | (m1_subset_1 @ (k2_funct_1 @ X50) @ 
% 33.42/33.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 33.42/33.63          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 33.42/33.63          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 33.42/33.63          | ~ (v1_funct_1 @ X50))),
% 33.42/33.63      inference('cnf', [status(esa)], [t31_funct_2])).
% 33.42/33.63  thf('16', plain,
% 33.42/33.63      ((~ (v1_funct_1 @ sk_B)
% 33.42/33.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 33.42/33.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 33.42/33.63        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 33.42/33.63        | ~ (v2_funct_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['14', '15'])).
% 33.42/33.63  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('19', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(redefinition_k2_relset_1, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i]:
% 33.42/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.42/33.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 33.42/33.63  thf('20', plain,
% 33.42/33.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 33.42/33.63         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 33.42/33.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 33.42/33.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 33.42/33.63  thf('21', plain,
% 33.42/33.63      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['19', '20'])).
% 33.42/33.63  thf('22', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(cc2_funct_2, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i]:
% 33.42/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.42/33.63       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 33.42/33.63         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 33.42/33.63  thf('23', plain,
% 33.42/33.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 33.42/33.63         (~ (v1_funct_1 @ X26)
% 33.42/33.63          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 33.42/33.63          | (v2_funct_2 @ X26 @ X28)
% 33.42/33.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 33.42/33.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 33.42/33.63  thf('24', plain,
% 33.42/33.63      (((v2_funct_2 @ sk_B @ sk_A)
% 33.42/33.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | ~ (v1_funct_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['22', '23'])).
% 33.42/33.63  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('27', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 33.42/33.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.42/33.63  thf(d3_funct_2, axiom,
% 33.42/33.63    (![A:$i,B:$i]:
% 33.42/33.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 33.42/33.63       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 33.42/33.63  thf('28', plain,
% 33.42/33.63      (![X37 : $i, X38 : $i]:
% 33.42/33.63         (~ (v2_funct_2 @ X38 @ X37)
% 33.42/33.63          | ((k2_relat_1 @ X38) = (X37))
% 33.42/33.63          | ~ (v5_relat_1 @ X38 @ X37)
% 33.42/33.63          | ~ (v1_relat_1 @ X38))),
% 33.42/33.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 33.42/33.63  thf('29', plain,
% 33.42/33.63      ((~ (v1_relat_1 @ sk_B)
% 33.42/33.63        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 33.42/33.63        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 33.42/33.63      inference('sup-', [status(thm)], ['27', '28'])).
% 33.42/33.63  thf('30', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(cc1_relset_1, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i]:
% 33.42/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.42/33.63       ( v1_relat_1 @ C ) ))).
% 33.42/33.63  thf('31', plain,
% 33.42/33.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 33.42/33.63         ((v1_relat_1 @ X10)
% 33.42/33.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 33.42/33.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 33.42/33.63  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 33.42/33.63      inference('sup-', [status(thm)], ['30', '31'])).
% 33.42/33.63  thf('33', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(cc2_relset_1, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i]:
% 33.42/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.42/33.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 33.42/33.63  thf('34', plain,
% 33.42/33.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 33.42/33.63         ((v5_relat_1 @ X13 @ X15)
% 33.42/33.63          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 33.42/33.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 33.42/33.63  thf('35', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 33.42/33.63      inference('sup-', [status(thm)], ['33', '34'])).
% 33.42/33.63  thf('36', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 33.42/33.63      inference('demod', [status(thm)], ['29', '32', '35'])).
% 33.42/33.63  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 33.42/33.63      inference('demod', [status(thm)], ['21', '36'])).
% 33.42/33.63  thf('38', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('39', plain,
% 33.42/33.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 33.42/33.63         (~ (v1_funct_1 @ X26)
% 33.42/33.63          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 33.42/33.63          | (v2_funct_1 @ X26)
% 33.42/33.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 33.42/33.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 33.42/33.63  thf('40', plain,
% 33.42/33.63      (((v2_funct_1 @ sk_B)
% 33.42/33.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | ~ (v1_funct_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['38', '39'])).
% 33.42/33.63  thf('41', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('43', plain, ((v2_funct_1 @ sk_B)),
% 33.42/33.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 33.42/33.63  thf('44', plain,
% 33.42/33.63      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 33.42/33.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 33.42/33.63        | ((sk_A) != (sk_A)))),
% 33.42/33.63      inference('demod', [status(thm)], ['16', '17', '18', '37', '43'])).
% 33.42/33.63  thf('45', plain,
% 33.42/33.63      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 33.42/33.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('simplify', [status(thm)], ['44'])).
% 33.42/33.63  thf('46', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf(redefinition_k1_partfun1, axiom,
% 33.42/33.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 33.42/33.63     ( ( ( v1_funct_1 @ E ) & 
% 33.42/33.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 33.42/33.63         ( v1_funct_1 @ F ) & 
% 33.42/33.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 33.42/33.63       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 33.42/33.63  thf('47', plain,
% 33.42/33.63      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 33.42/33.63         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 33.42/33.63          | ~ (v1_funct_1 @ X41)
% 33.42/33.63          | ~ (v1_funct_1 @ X44)
% 33.42/33.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 33.42/33.63          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 33.42/33.63              = (k5_relat_1 @ X41 @ X44)))),
% 33.42/33.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 33.42/33.63  thf('48', plain,
% 33.42/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.42/33.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 33.42/33.63            = (k5_relat_1 @ sk_B @ X0))
% 33.42/33.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.42/33.63          | ~ (v1_funct_1 @ X0)
% 33.42/33.63          | ~ (v1_funct_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['46', '47'])).
% 33.42/33.63  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('50', plain,
% 33.42/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.42/33.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 33.42/33.63            = (k5_relat_1 @ sk_B @ X0))
% 33.42/33.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.42/33.63          | ~ (v1_funct_1 @ X0))),
% 33.42/33.63      inference('demod', [status(thm)], ['48', '49'])).
% 33.42/33.63  thf('51', plain,
% 33.42/33.63      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 33.42/33.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.42/33.63            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 33.42/33.63      inference('sup-', [status(thm)], ['45', '50'])).
% 33.42/33.63  thf('52', plain,
% 33.42/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('53', plain,
% 33.42/33.63      (![X50 : $i, X51 : $i, X52 : $i]:
% 33.42/33.63         (~ (v2_funct_1 @ X50)
% 33.42/33.63          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 33.42/33.63          | (v1_funct_1 @ (k2_funct_1 @ X50))
% 33.42/33.63          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 33.42/33.63          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 33.42/33.63          | ~ (v1_funct_1 @ X50))),
% 33.42/33.63      inference('cnf', [status(esa)], [t31_funct_2])).
% 33.42/33.63  thf('54', plain,
% 33.42/33.63      ((~ (v1_funct_1 @ sk_B)
% 33.42/33.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 33.42/33.63        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 33.42/33.63        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 33.42/33.63        | ~ (v2_funct_1 @ sk_B))),
% 33.42/33.63      inference('sup-', [status(thm)], ['52', '53'])).
% 33.42/33.63  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.42/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.42/33.63  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 33.42/33.63      inference('demod', [status(thm)], ['21', '36'])).
% 33.42/33.63  thf('58', plain, ((v2_funct_1 @ sk_B)),
% 33.42/33.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 33.42/33.63  thf('59', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_B)) | ((sk_A) != (sk_A)))),
% 33.42/33.63      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 33.42/33.63  thf('60', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 33.42/33.63      inference('simplify', [status(thm)], ['59'])).
% 33.42/33.63  thf('61', plain,
% 33.42/33.63      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 33.42/33.63         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 33.42/33.63      inference('demod', [status(thm)], ['51', '60'])).
% 33.42/33.63  thf('62', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 33.42/33.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 33.42/33.63  thf('63', plain,
% 33.42/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.42/33.63            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.42/33.63           (k6_partfun1 @ sk_A)))
% 33.42/33.63         <= (~
% 33.42/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.42/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.42/33.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.42/33.63               (k6_partfun1 @ sk_A))))),
% 33.42/33.63      inference('split', [status(esa)], ['1'])).
% 33.42/33.63  thf('64', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 33.42/33.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.45/33.63  thf('65', plain,
% 33.45/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63           (k6_relat_1 @ sk_A)))
% 33.45/33.63         <= (~
% 33.45/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63               (k6_partfun1 @ sk_A))))),
% 33.45/33.63      inference('demod', [status(thm)], ['63', '64'])).
% 33.45/33.63  thf('66', plain,
% 33.45/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63            (k2_funct_1 @ sk_B)) @ 
% 33.45/33.63           (k6_relat_1 @ sk_A)))
% 33.45/33.63         <= (~
% 33.45/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63               (k6_partfun1 @ sk_A))))),
% 33.45/33.63      inference('sup-', [status(thm)], ['62', '65'])).
% 33.45/33.63  thf('67', plain,
% 33.45/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 33.45/33.63         <= (~
% 33.45/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63               (k6_partfun1 @ sk_A))))),
% 33.45/33.63      inference('sup-', [status(thm)], ['61', '66'])).
% 33.45/33.63  thf('68', plain,
% 33.45/33.63      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 33.45/33.63            (k6_relat_1 @ sk_A))
% 33.45/33.63         | ~ (v1_relat_1 @ sk_B)
% 33.45/33.63         | ~ (v1_funct_1 @ sk_B)
% 33.45/33.63         | ~ (v2_funct_1 @ sk_B)))
% 33.45/33.63         <= (~
% 33.45/33.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63               (k6_partfun1 @ sk_A))))),
% 33.45/33.63      inference('sup-', [status(thm)], ['13', '67'])).
% 33.45/33.63  thf('69', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf(d1_funct_2, axiom,
% 33.45/33.63    (![A:$i,B:$i,C:$i]:
% 33.45/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.45/33.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 33.45/33.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 33.45/33.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 33.45/33.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 33.45/33.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 33.45/33.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 33.45/33.63  thf(zf_stmt_1, axiom,
% 33.45/33.63    (![C:$i,B:$i,A:$i]:
% 33.45/33.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 33.45/33.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 33.45/33.63  thf('70', plain,
% 33.45/33.63      (![X31 : $i, X32 : $i, X33 : $i]:
% 33.45/33.63         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 33.45/33.63          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 33.45/33.63          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 33.45/33.63  thf('71', plain,
% 33.45/33.63      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 33.45/33.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 33.45/33.63      inference('sup-', [status(thm)], ['69', '70'])).
% 33.45/33.63  thf('72', plain,
% 33.45/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 33.45/33.63  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 33.45/33.63  thf(zf_stmt_4, axiom,
% 33.45/33.63    (![B:$i,A:$i]:
% 33.45/33.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 33.45/33.63       ( zip_tseitin_0 @ B @ A ) ))).
% 33.45/33.63  thf(zf_stmt_5, axiom,
% 33.45/33.63    (![A:$i,B:$i,C:$i]:
% 33.45/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.45/33.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 33.45/33.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 33.45/33.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 33.45/33.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 33.45/33.63  thf('73', plain,
% 33.45/33.63      (![X34 : $i, X35 : $i, X36 : $i]:
% 33.45/33.63         (~ (zip_tseitin_0 @ X34 @ X35)
% 33.45/33.63          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 33.45/33.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 33.45/33.63  thf('74', plain,
% 33.45/33.63      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 33.45/33.63      inference('sup-', [status(thm)], ['72', '73'])).
% 33.45/33.63  thf('75', plain,
% 33.45/33.63      (![X29 : $i, X30 : $i]:
% 33.45/33.63         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 33.45/33.63  thf('76', plain,
% 33.45/33.63      (![X29 : $i, X30 : $i]:
% 33.45/33.63         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 33.45/33.63  thf('77', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 33.45/33.63      inference('simplify', [status(thm)], ['76'])).
% 33.45/33.63  thf('78', plain,
% 33.45/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.45/33.63         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 33.45/33.63      inference('sup+', [status(thm)], ['75', '77'])).
% 33.45/33.63  thf('79', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 33.45/33.63      inference('eq_fact', [status(thm)], ['78'])).
% 33.45/33.63  thf('80', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 33.45/33.63      inference('demod', [status(thm)], ['74', '79'])).
% 33.45/33.63  thf('81', plain,
% 33.45/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf(redefinition_k1_relset_1, axiom,
% 33.45/33.63    (![A:$i,B:$i,C:$i]:
% 33.45/33.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.45/33.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 33.45/33.63  thf('82', plain,
% 33.45/33.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 33.45/33.63         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 33.45/33.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 33.45/33.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 33.45/33.63  thf('83', plain,
% 33.45/33.63      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 33.45/33.63      inference('sup-', [status(thm)], ['81', '82'])).
% 33.45/33.63  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 33.45/33.63      inference('demod', [status(thm)], ['71', '80', '83'])).
% 33.45/33.63  thf(dt_k6_partfun1, axiom,
% 33.45/33.63    (![A:$i]:
% 33.45/33.63     ( ( m1_subset_1 @
% 33.45/33.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 33.45/33.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 33.45/33.63  thf('85', plain,
% 33.45/33.63      (![X40 : $i]:
% 33.45/33.63         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 33.45/33.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 33.45/33.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 33.45/33.63  thf('86', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 33.45/33.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.45/33.63  thf('87', plain,
% 33.45/33.63      (![X40 : $i]:
% 33.45/33.63         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 33.45/33.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 33.45/33.63      inference('demod', [status(thm)], ['85', '86'])).
% 33.45/33.63  thf(reflexivity_r2_relset_1, axiom,
% 33.45/33.63    (![A:$i,B:$i,C:$i,D:$i]:
% 33.45/33.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 33.45/33.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.45/33.63       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 33.45/33.63  thf('88', plain,
% 33.45/33.63      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 33.45/33.63         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 33.45/33.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 33.45/33.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 33.45/33.63      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 33.45/33.63  thf('89', plain,
% 33.45/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.45/33.63         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 33.45/33.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 33.45/33.63      inference('condensation', [status(thm)], ['88'])).
% 33.45/33.63  thf('90', plain,
% 33.45/33.63      (![X0 : $i]:
% 33.45/33.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 33.45/33.63      inference('sup-', [status(thm)], ['87', '89'])).
% 33.45/33.63  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 33.45/33.63      inference('sup-', [status(thm)], ['30', '31'])).
% 33.45/33.63  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf('93', plain, ((v2_funct_1 @ sk_B)),
% 33.45/33.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 33.45/33.63  thf('94', plain,
% 33.45/33.63      (((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63         (k6_partfun1 @ sk_A)))),
% 33.45/33.63      inference('demod', [status(thm)], ['68', '84', '90', '91', '92', '93'])).
% 33.45/33.63  thf('95', plain,
% 33.45/33.63      (~
% 33.45/33.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.45/33.63          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.45/33.63         (k6_partfun1 @ sk_A))) | 
% 33.45/33.63       ~
% 33.45/33.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 33.45/33.63          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 33.45/33.63         (k6_partfun1 @ sk_A)))),
% 33.45/33.63      inference('split', [status(esa)], ['1'])).
% 33.45/33.63  thf('96', plain,
% 33.45/33.63      (~
% 33.45/33.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 33.45/33.63          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 33.45/33.63         (k6_partfun1 @ sk_A)))),
% 33.45/33.63      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 33.45/33.63  thf('97', plain,
% 33.45/33.63      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 33.45/33.63          (k6_relat_1 @ sk_A))),
% 33.45/33.63      inference('simpl_trail', [status(thm)], ['12', '96'])).
% 33.45/33.63  thf('98', plain,
% 33.45/33.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf('99', plain,
% 33.45/33.63      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 33.45/33.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.45/33.63      inference('simplify', [status(thm)], ['44'])).
% 33.45/33.63  thf('100', plain,
% 33.45/33.63      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 33.45/33.63         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 33.45/33.63          | ~ (v1_funct_1 @ X41)
% 33.45/33.63          | ~ (v1_funct_1 @ X44)
% 33.45/33.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 33.45/33.63          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 33.45/33.63              = (k5_relat_1 @ X41 @ X44)))),
% 33.45/33.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 33.45/33.63  thf('101', plain,
% 33.45/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.45/33.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 33.45/33.63            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 33.45/33.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.45/33.63          | ~ (v1_funct_1 @ X0)
% 33.45/33.63          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 33.45/33.63      inference('sup-', [status(thm)], ['99', '100'])).
% 33.45/33.63  thf('102', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 33.45/33.63      inference('simplify', [status(thm)], ['59'])).
% 33.45/33.63  thf('103', plain,
% 33.45/33.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.45/33.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 33.45/33.63            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 33.45/33.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.45/33.63          | ~ (v1_funct_1 @ X0))),
% 33.45/33.63      inference('demod', [status(thm)], ['101', '102'])).
% 33.45/33.63  thf('104', plain,
% 33.45/33.63      ((~ (v1_funct_1 @ sk_B)
% 33.45/33.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 33.45/33.63            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 33.45/33.63      inference('sup-', [status(thm)], ['98', '103'])).
% 33.45/33.63  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf('106', plain,
% 33.45/33.63      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 33.45/33.63         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 33.45/33.63      inference('demod', [status(thm)], ['104', '105'])).
% 33.45/33.63  thf('107', plain,
% 33.45/33.63      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 33.45/33.63          (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 33.45/33.63      inference('demod', [status(thm)], ['97', '106'])).
% 33.45/33.63  thf('108', plain,
% 33.45/33.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 33.45/33.63           (k6_relat_1 @ sk_A))
% 33.45/33.63        | ~ (v1_relat_1 @ sk_B)
% 33.45/33.63        | ~ (v1_funct_1 @ sk_B)
% 33.45/33.63        | ~ (v2_funct_1 @ sk_B))),
% 33.45/33.63      inference('sup-', [status(thm)], ['0', '107'])).
% 33.45/33.63  thf('109', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 33.45/33.63      inference('demod', [status(thm)], ['29', '32', '35'])).
% 33.45/33.63  thf('110', plain,
% 33.45/33.63      (![X0 : $i]:
% 33.45/33.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 33.45/33.63      inference('sup-', [status(thm)], ['87', '89'])).
% 33.45/33.63  thf('111', plain, ((v1_relat_1 @ sk_B)),
% 33.45/33.63      inference('sup-', [status(thm)], ['30', '31'])).
% 33.45/33.63  thf('112', plain, ((v1_funct_1 @ sk_B)),
% 33.45/33.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.45/33.63  thf('113', plain, ((v2_funct_1 @ sk_B)),
% 33.45/33.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 33.45/33.63  thf('114', plain, ($false),
% 33.45/33.63      inference('demod', [status(thm)],
% 33.45/33.63                ['108', '109', '110', '111', '112', '113'])).
% 33.45/33.63  
% 33.45/33.63  % SZS output end Refutation
% 33.45/33.63  
% 33.45/33.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
