%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fEHDmHHPKk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 5.91s
% Output     : Refutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  162 (1054 expanded)
%              Number of leaves         :   44 ( 330 expanded)
%              Depth                    :   14
%              Number of atoms          : 1261 (25952 expanded)
%              Number of equality atoms :   89 ( 480 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('12',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_funct_2 @ X43 @ X42 )
        = ( k2_funct_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('31',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_partfun1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('32',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_relat_1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_2 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('48',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','56','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['45','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','61','67'])).

thf('69',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('83',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['26','75','76','78','79','80','81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('86',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('87',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','94'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('96',plain,(
    ! [X12: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X12 ) )
      = ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('97',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','94'])).

thf('99',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','83','99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('109',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('110',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('113',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('114',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['106','107','108','109','110','111','112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['101','114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fEHDmHHPKk
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.91/6.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.91/6.11  % Solved by: fo/fo7.sh
% 5.91/6.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.91/6.11  % done 6882 iterations in 5.657s
% 5.91/6.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.91/6.11  % SZS output start Refutation
% 5.91/6.11  thf(sk_A_type, type, sk_A: $i).
% 5.91/6.11  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.91/6.11  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 5.91/6.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.91/6.11  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.91/6.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.91/6.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.91/6.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.91/6.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.91/6.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.91/6.11  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.91/6.11  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.91/6.11  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.91/6.11  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.91/6.11  thf(sk_C_type, type, sk_C: $i).
% 5.91/6.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.91/6.11  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.91/6.11  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.91/6.11  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.91/6.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.91/6.11  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 5.91/6.11  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.91/6.11  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.91/6.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.91/6.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.91/6.11  thf(sk_B_type, type, sk_B: $i).
% 5.91/6.11  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.91/6.11  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.11  thf(t8_boole, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.91/6.11  thf('1', plain,
% 5.91/6.11      (![X4 : $i, X5 : $i]:
% 5.91/6.11         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t8_boole])).
% 5.91/6.11  thf('2', plain,
% 5.91/6.11      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.91/6.11      inference('sup-', [status(thm)], ['0', '1'])).
% 5.91/6.11  thf('3', plain,
% 5.91/6.11      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.91/6.11      inference('sup-', [status(thm)], ['0', '1'])).
% 5.91/6.11  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.91/6.11  thf('4', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.91/6.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.91/6.11  thf(t3_subset, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.91/6.11  thf('5', plain,
% 5.91/6.11      (![X9 : $i, X11 : $i]:
% 5.91/6.11         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 5.91/6.11      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.11  thf('6', plain,
% 5.91/6.11      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 5.91/6.11      inference('sup-', [status(thm)], ['4', '5'])).
% 5.91/6.11  thf(redefinition_r2_relset_1, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i,D:$i]:
% 5.91/6.11     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.91/6.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.11       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.91/6.11  thf('7', plain,
% 5.91/6.11      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.11         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.91/6.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.91/6.11          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 5.91/6.11          | ((X25) != (X28)))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.91/6.11  thf('8', plain,
% 5.91/6.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.11         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 5.91/6.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.91/6.11      inference('simplify', [status(thm)], ['7'])).
% 5.91/6.11  thf('9', plain,
% 5.91/6.11      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.91/6.11      inference('sup-', [status(thm)], ['6', '8'])).
% 5.91/6.11  thf('10', plain,
% 5.91/6.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.91/6.11         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.91/6.11      inference('sup+', [status(thm)], ['3', '9'])).
% 5.91/6.11  thf('11', plain,
% 5.91/6.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.91/6.11         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.91/6.11          | ~ (v1_xboole_0 @ X0)
% 5.91/6.11          | ~ (v1_xboole_0 @ X1))),
% 5.91/6.11      inference('sup+', [status(thm)], ['2', '10'])).
% 5.91/6.11  thf(t87_funct_2, conjecture,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.91/6.11         ( v3_funct_2 @ B @ A @ A ) & 
% 5.91/6.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.91/6.11       ( ![C:$i]:
% 5.91/6.11         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.91/6.11             ( v3_funct_2 @ C @ A @ A ) & 
% 5.91/6.11             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.91/6.11           ( ( r2_relset_1 @
% 5.91/6.11               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.91/6.11               ( k6_partfun1 @ A ) ) =>
% 5.91/6.11             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 5.91/6.11  thf(zf_stmt_0, negated_conjecture,
% 5.91/6.11    (~( ![A:$i,B:$i]:
% 5.91/6.11        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.91/6.11            ( v3_funct_2 @ B @ A @ A ) & 
% 5.91/6.11            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.91/6.11          ( ![C:$i]:
% 5.91/6.11            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.91/6.11                ( v3_funct_2 @ C @ A @ A ) & 
% 5.91/6.11                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.91/6.11              ( ( r2_relset_1 @
% 5.91/6.11                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.91/6.11                  ( k6_partfun1 @ A ) ) =>
% 5.91/6.11                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 5.91/6.11    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 5.91/6.11  thf('12', plain,
% 5.91/6.11      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('13', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(redefinition_k2_funct_2, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.91/6.11         ( v3_funct_2 @ B @ A @ A ) & 
% 5.91/6.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.91/6.11       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 5.91/6.11  thf('14', plain,
% 5.91/6.11      (![X42 : $i, X43 : $i]:
% 5.91/6.11         (((k2_funct_2 @ X43 @ X42) = (k2_funct_1 @ X42))
% 5.91/6.11          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))
% 5.91/6.11          | ~ (v3_funct_2 @ X42 @ X43 @ X43)
% 5.91/6.11          | ~ (v1_funct_2 @ X42 @ X43 @ X43)
% 5.91/6.11          | ~ (v1_funct_1 @ X42))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 5.91/6.11  thf('15', plain,
% 5.91/6.11      ((~ (v1_funct_1 @ sk_B)
% 5.91/6.11        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.91/6.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.91/6.11        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['13', '14'])).
% 5.91/6.11  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 5.91/6.11      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 5.91/6.11  thf('20', plain,
% 5.91/6.11      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 5.91/6.11      inference('demod', [status(thm)], ['12', '19'])).
% 5.91/6.11  thf('21', plain,
% 5.91/6.11      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['11', '20'])).
% 5.91/6.11  thf('22', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('23', plain,
% 5.91/6.11      (![X9 : $i, X10 : $i]:
% 5.91/6.11         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.11  thf('24', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.91/6.11      inference('sup-', [status(thm)], ['22', '23'])).
% 5.91/6.11  thf(d10_xboole_0, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.91/6.11  thf('25', plain,
% 5.91/6.11      (![X0 : $i, X2 : $i]:
% 5.91/6.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.91/6.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.91/6.11  thf('26', plain,
% 5.91/6.11      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 5.91/6.11        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['24', '25'])).
% 5.91/6.11  thf('27', plain,
% 5.91/6.11      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.91/6.11        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.91/6.11        (k6_partfun1 @ sk_A))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(redefinition_k6_partfun1, axiom,
% 5.91/6.11    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.91/6.11  thf('28', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.91/6.11  thf('29', plain,
% 5.91/6.11      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.91/6.11        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 5.91/6.11        (k6_relat_1 @ sk_A))),
% 5.91/6.11      inference('demod', [status(thm)], ['27', '28'])).
% 5.91/6.11  thf('30', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(t36_funct_2, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i]:
% 5.91/6.11     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.91/6.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.11       ( ![D:$i]:
% 5.91/6.11         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.91/6.11             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.91/6.11           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.91/6.11               ( r2_relset_1 @
% 5.91/6.11                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.91/6.11                 ( k6_partfun1 @ A ) ) & 
% 5.91/6.11               ( v2_funct_1 @ C ) ) =>
% 5.91/6.11             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.91/6.11               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.91/6.11  thf('31', plain,
% 5.91/6.11      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X49)
% 5.91/6.11          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 5.91/6.11          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.91/6.11          | ((X49) = (k2_funct_1 @ X52))
% 5.91/6.11          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 5.91/6.11               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 5.91/6.11               (k6_partfun1 @ X51))
% 5.91/6.11          | ((X50) = (k1_xboole_0))
% 5.91/6.11          | ((X51) = (k1_xboole_0))
% 5.91/6.11          | ~ (v2_funct_1 @ X52)
% 5.91/6.11          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 5.91/6.11          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 5.91/6.11          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 5.91/6.11          | ~ (v1_funct_1 @ X52))),
% 5.91/6.11      inference('cnf', [status(esa)], [t36_funct_2])).
% 5.91/6.11  thf('32', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.91/6.11  thf('33', plain,
% 5.91/6.11      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X49)
% 5.91/6.11          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 5.91/6.11          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.91/6.11          | ((X49) = (k2_funct_1 @ X52))
% 5.91/6.11          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 5.91/6.11               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 5.91/6.11               (k6_relat_1 @ X51))
% 5.91/6.11          | ((X50) = (k1_xboole_0))
% 5.91/6.11          | ((X51) = (k1_xboole_0))
% 5.91/6.11          | ~ (v2_funct_1 @ X52)
% 5.91/6.11          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 5.91/6.11          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 5.91/6.11          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 5.91/6.11          | ~ (v1_funct_1 @ X52))),
% 5.91/6.11      inference('demod', [status(thm)], ['31', '32'])).
% 5.91/6.11  thf('34', plain,
% 5.91/6.11      (![X0 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X0)
% 5.91/6.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.91/6.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.91/6.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.91/6.11          | ~ (v2_funct_1 @ X0)
% 5.91/6.11          | ((sk_A) = (k1_xboole_0))
% 5.91/6.11          | ((sk_A) = (k1_xboole_0))
% 5.91/6.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.91/6.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.91/6.11               (k6_relat_1 @ sk_A))
% 5.91/6.11          | ((sk_C) = (k2_funct_1 @ X0))
% 5.91/6.11          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 5.91/6.11          | ~ (v1_funct_1 @ sk_C))),
% 5.91/6.11      inference('sup-', [status(thm)], ['30', '33'])).
% 5.91/6.11  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('37', plain,
% 5.91/6.11      (![X0 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X0)
% 5.91/6.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.91/6.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.91/6.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.91/6.11          | ~ (v2_funct_1 @ X0)
% 5.91/6.11          | ((sk_A) = (k1_xboole_0))
% 5.91/6.11          | ((sk_A) = (k1_xboole_0))
% 5.91/6.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.91/6.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.91/6.11               (k6_relat_1 @ sk_A))
% 5.91/6.11          | ((sk_C) = (k2_funct_1 @ X0)))),
% 5.91/6.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 5.91/6.11  thf('38', plain,
% 5.91/6.11      (![X0 : $i]:
% 5.91/6.11         (((sk_C) = (k2_funct_1 @ X0))
% 5.91/6.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.91/6.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.91/6.11               (k6_relat_1 @ sk_A))
% 5.91/6.11          | ((sk_A) = (k1_xboole_0))
% 5.91/6.11          | ~ (v2_funct_1 @ X0)
% 5.91/6.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.91/6.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.91/6.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.91/6.11          | ~ (v1_funct_1 @ X0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['37'])).
% 5.91/6.11  thf('39', plain,
% 5.91/6.11      ((~ (v1_funct_1 @ sk_B)
% 5.91/6.11        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.91/6.11        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.91/6.11        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 5.91/6.11        | ~ (v2_funct_1 @ sk_B)
% 5.91/6.11        | ((sk_A) = (k1_xboole_0))
% 5.91/6.11        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['29', '38'])).
% 5.91/6.11  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('41', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('42', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('43', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(redefinition_k2_relset_1, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i]:
% 5.91/6.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.11       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.91/6.11  thf('44', plain,
% 5.91/6.11      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.91/6.11         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 5.91/6.11          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.91/6.11  thf('45', plain,
% 5.91/6.11      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 5.91/6.11      inference('sup-', [status(thm)], ['43', '44'])).
% 5.91/6.11  thf('46', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(cc2_funct_2, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i]:
% 5.91/6.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.11       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 5.91/6.11         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 5.91/6.11  thf('47', plain,
% 5.91/6.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X29)
% 5.91/6.11          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 5.91/6.11          | (v2_funct_2 @ X29 @ X31)
% 5.91/6.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 5.91/6.11      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.91/6.11  thf('48', plain,
% 5.91/6.11      (((v2_funct_2 @ sk_B @ sk_A)
% 5.91/6.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.91/6.11        | ~ (v1_funct_1 @ sk_B))),
% 5.91/6.11      inference('sup-', [status(thm)], ['46', '47'])).
% 5.91/6.11  thf('49', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('51', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 5.91/6.11      inference('demod', [status(thm)], ['48', '49', '50'])).
% 5.91/6.11  thf(d3_funct_2, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.91/6.11       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.91/6.11  thf('52', plain,
% 5.91/6.11      (![X32 : $i, X33 : $i]:
% 5.91/6.11         (~ (v2_funct_2 @ X33 @ X32)
% 5.91/6.11          | ((k2_relat_1 @ X33) = (X32))
% 5.91/6.11          | ~ (v5_relat_1 @ X33 @ X32)
% 5.91/6.11          | ~ (v1_relat_1 @ X33))),
% 5.91/6.11      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.91/6.11  thf('53', plain,
% 5.91/6.11      ((~ (v1_relat_1 @ sk_B)
% 5.91/6.11        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 5.91/6.11        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['51', '52'])).
% 5.91/6.11  thf('54', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(cc1_relset_1, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i]:
% 5.91/6.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.11       ( v1_relat_1 @ C ) ))).
% 5.91/6.11  thf('55', plain,
% 5.91/6.11      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.91/6.11         ((v1_relat_1 @ X13)
% 5.91/6.11          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 5.91/6.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.91/6.11  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 5.91/6.11      inference('sup-', [status(thm)], ['54', '55'])).
% 5.91/6.11  thf('57', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf(cc2_relset_1, axiom,
% 5.91/6.11    (![A:$i,B:$i,C:$i]:
% 5.91/6.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.11       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.91/6.11  thf('58', plain,
% 5.91/6.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.91/6.11         ((v5_relat_1 @ X16 @ X18)
% 5.91/6.11          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.91/6.11      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.91/6.11  thf('59', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 5.91/6.11      inference('sup-', [status(thm)], ['57', '58'])).
% 5.91/6.11  thf('60', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 5.91/6.11      inference('demod', [status(thm)], ['53', '56', '59'])).
% 5.91/6.11  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 5.91/6.11      inference('demod', [status(thm)], ['45', '60'])).
% 5.91/6.11  thf('62', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('63', plain,
% 5.91/6.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.91/6.11         (~ (v1_funct_1 @ X29)
% 5.91/6.11          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 5.91/6.11          | (v2_funct_1 @ X29)
% 5.91/6.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 5.91/6.11      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.91/6.11  thf('64', plain,
% 5.91/6.11      (((v2_funct_1 @ sk_B)
% 5.91/6.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.91/6.11        | ~ (v1_funct_1 @ sk_B))),
% 5.91/6.11      inference('sup-', [status(thm)], ['62', '63'])).
% 5.91/6.11  thf('65', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 5.91/6.11      inference('demod', [status(thm)], ['64', '65', '66'])).
% 5.91/6.11  thf('68', plain,
% 5.91/6.11      ((((sk_A) != (sk_A))
% 5.91/6.11        | ((sk_A) = (k1_xboole_0))
% 5.91/6.11        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 5.91/6.11      inference('demod', [status(thm)], ['39', '40', '41', '42', '61', '67'])).
% 5.91/6.11  thf('69', plain,
% 5.91/6.11      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 5.91/6.11      inference('simplify', [status(thm)], ['68'])).
% 5.91/6.11  thf('70', plain,
% 5.91/6.11      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 5.91/6.11      inference('demod', [status(thm)], ['12', '19'])).
% 5.91/6.11  thf('71', plain,
% 5.91/6.11      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['69', '70'])).
% 5.91/6.11  thf('72', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('73', plain,
% 5.91/6.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.11         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 5.91/6.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.91/6.11      inference('simplify', [status(thm)], ['7'])).
% 5.91/6.11  thf('74', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 5.91/6.11      inference('sup-', [status(thm)], ['72', '73'])).
% 5.91/6.11  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf(t113_zfmisc_1, axiom,
% 5.91/6.11    (![A:$i,B:$i]:
% 5.91/6.11     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.91/6.11       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.91/6.11  thf('77', plain,
% 5.91/6.11      (![X7 : $i, X8 : $i]:
% 5.91/6.11         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.91/6.11  thf('78', plain,
% 5.91/6.11      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['77'])).
% 5.91/6.11  thf('79', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.91/6.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.91/6.11  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('82', plain,
% 5.91/6.11      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['77'])).
% 5.91/6.11  thf('83', plain, (((k1_xboole_0) = (sk_B))),
% 5.91/6.11      inference('demod', [status(thm)],
% 5.91/6.11                ['26', '75', '76', '78', '79', '80', '81', '82'])).
% 5.91/6.11  thf('84', plain,
% 5.91/6.11      (![X7 : $i, X8 : $i]:
% 5.91/6.11         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.91/6.11  thf('85', plain,
% 5.91/6.11      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['84'])).
% 5.91/6.11  thf(dt_k6_partfun1, axiom,
% 5.91/6.11    (![A:$i]:
% 5.91/6.11     ( ( m1_subset_1 @
% 5.91/6.11         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.91/6.11       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.91/6.11  thf('86', plain,
% 5.91/6.11      (![X41 : $i]:
% 5.91/6.11         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 5.91/6.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 5.91/6.11      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.91/6.11  thf('87', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.91/6.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.91/6.11  thf('88', plain,
% 5.91/6.11      (![X41 : $i]:
% 5.91/6.11         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 5.91/6.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 5.91/6.11      inference('demod', [status(thm)], ['86', '87'])).
% 5.91/6.11  thf('89', plain,
% 5.91/6.11      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.91/6.11      inference('sup+', [status(thm)], ['85', '88'])).
% 5.91/6.11  thf('90', plain,
% 5.91/6.11      (![X9 : $i, X10 : $i]:
% 5.91/6.11         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.11  thf('91', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 5.91/6.11      inference('sup-', [status(thm)], ['89', '90'])).
% 5.91/6.11  thf('92', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.91/6.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.91/6.11  thf('93', plain,
% 5.91/6.11      (![X0 : $i, X2 : $i]:
% 5.91/6.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.91/6.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.91/6.11  thf('94', plain,
% 5.91/6.11      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['92', '93'])).
% 5.91/6.11  thf('95', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.11      inference('sup-', [status(thm)], ['91', '94'])).
% 5.91/6.11  thf(t67_funct_1, axiom,
% 5.91/6.11    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 5.91/6.11  thf('96', plain,
% 5.91/6.11      (![X12 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X12)) = (k6_relat_1 @ X12))),
% 5.91/6.11      inference('cnf', [status(esa)], [t67_funct_1])).
% 5.91/6.11  thf('97', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.91/6.11      inference('sup+', [status(thm)], ['95', '96'])).
% 5.91/6.11  thf('98', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.11      inference('sup-', [status(thm)], ['91', '94'])).
% 5.91/6.11  thf('99', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.11      inference('sup+', [status(thm)], ['97', '98'])).
% 5.91/6.11  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.11  thf('101', plain, (~ (v1_xboole_0 @ sk_C)),
% 5.91/6.11      inference('demod', [status(thm)], ['21', '83', '99', '100'])).
% 5.91/6.11  thf('102', plain,
% 5.91/6.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.91/6.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.11  thf('103', plain,
% 5.91/6.11      (![X9 : $i, X10 : $i]:
% 5.91/6.11         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.91/6.11      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.11  thf('104', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.91/6.11      inference('sup-', [status(thm)], ['102', '103'])).
% 5.91/6.11  thf('105', plain,
% 5.91/6.11      (![X0 : $i, X2 : $i]:
% 5.91/6.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.91/6.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.91/6.11  thf('106', plain,
% 5.91/6.11      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 5.91/6.11        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 5.91/6.11      inference('sup-', [status(thm)], ['104', '105'])).
% 5.91/6.11  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('109', plain,
% 5.91/6.11      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['77'])).
% 5.91/6.11  thf('110', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.91/6.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.91/6.11  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 5.91/6.11      inference('demod', [status(thm)], ['71', '74'])).
% 5.91/6.11  thf('113', plain,
% 5.91/6.11      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 5.91/6.11      inference('simplify', [status(thm)], ['77'])).
% 5.91/6.11  thf('114', plain, (((k1_xboole_0) = (sk_C))),
% 5.91/6.11      inference('demod', [status(thm)],
% 5.91/6.11                ['106', '107', '108', '109', '110', '111', '112', '113'])).
% 5.91/6.11  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.11  thf('116', plain, ($false),
% 5.91/6.11      inference('demod', [status(thm)], ['101', '114', '115'])).
% 5.91/6.11  
% 5.91/6.11  % SZS output end Refutation
% 5.91/6.11  
% 5.91/6.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
