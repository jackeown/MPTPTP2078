%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nj5BLNQBxa

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:49 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  218 (7565 expanded)
%              Number of leaves         :   37 (2235 expanded)
%              Depth                    :   28
%              Number of atoms          : 1898 (118949 expanded)
%              Number of equality atoms :  102 (5180 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t31_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['2','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','44','45','46','47'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('52',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('55',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('56',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['52','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('85',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('87',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,(
    ! [X30: $i] :
      ( ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['83','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','103'])).

thf('105',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('113',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('114',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('117',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','113','114','115','116'])).

thf('118',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['104','117'])).

thf('119',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','113','114','115','116'])).

thf('120',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('123',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('124',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('129',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('131',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('133',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('134',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('135',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','113','114','115','116'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','113','114','115','116'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['131','132','135','138','141'])).

thf('143',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['118','148'])).

thf('150',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('151',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('152',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','127','128'])).

thf('154',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['133','134'])).

thf('155',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('156',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('157',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('159',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('166',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('168',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('172',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['164','170','171'])).

thf('173',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['149','172'])).

thf('174',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('175',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['77','173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['70','175'])).

thf('177',plain,
    ( $false
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','176'])).

thf('178',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['77','173','174'])).

thf('179',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['177','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nj5BLNQBxa
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.75  % Solved by: fo/fo7.sh
% 1.51/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.75  % done 1560 iterations in 1.294s
% 1.51/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.75  % SZS output start Refutation
% 1.51/1.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.51/1.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.51/1.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.75  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.51/1.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.51/1.75  thf(t31_funct_2, conjecture,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.75       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.51/1.75         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.51/1.75           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.51/1.75           ( m1_subset_1 @
% 1.51/1.75             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.51/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.75    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.75          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.51/1.75            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.51/1.75              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.51/1.75              ( m1_subset_1 @
% 1.51/1.75                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.51/1.75    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.51/1.75  thf('0', plain,
% 1.51/1.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.51/1.75        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('1', plain,
% 1.51/1.75      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf(t55_funct_1, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.75       ( ( v2_funct_1 @ A ) =>
% 1.51/1.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.51/1.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.51/1.75  thf('2', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf(dt_k2_funct_1, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.51/1.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.51/1.75  thf('3', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('4', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf(d1_funct_2, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.51/1.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.51/1.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.51/1.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.51/1.75  thf(zf_stmt_1, axiom,
% 1.51/1.75    (![B:$i,A:$i]:
% 1.51/1.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.75       ( zip_tseitin_0 @ B @ A ) ))).
% 1.51/1.75  thf('5', plain,
% 1.51/1.75      (![X22 : $i, X23 : $i]:
% 1.51/1.75         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.75  thf(t113_zfmisc_1, axiom,
% 1.51/1.75    (![A:$i,B:$i]:
% 1.51/1.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.51/1.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.51/1.75  thf('6', plain,
% 1.51/1.75      (![X5 : $i, X6 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.51/1.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.51/1.75  thf('7', plain,
% 1.51/1.75      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['6'])).
% 1.51/1.75  thf('8', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.75      inference('sup+', [status(thm)], ['5', '7'])).
% 1.51/1.75  thf(t3_funct_2, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.75       ( ( v1_funct_1 @ A ) & 
% 1.51/1.75         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.51/1.75         ( m1_subset_1 @
% 1.51/1.75           A @ 
% 1.51/1.75           ( k1_zfmisc_1 @
% 1.51/1.75             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.75  thf('9', plain,
% 1.51/1.75      (![X30 : $i]:
% 1.51/1.75         ((m1_subset_1 @ X30 @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 1.51/1.75          | ~ (v1_funct_1 @ X30)
% 1.51/1.75          | ~ (v1_relat_1 @ X30))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.51/1.75  thf('10', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.51/1.75          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0))),
% 1.51/1.75      inference('sup+', [status(thm)], ['8', '9'])).
% 1.51/1.75  thf('11', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.51/1.75      inference('sup+', [status(thm)], ['5', '7'])).
% 1.51/1.75  thf('12', plain,
% 1.51/1.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.51/1.75  thf(zf_stmt_3, axiom,
% 1.51/1.75    (![C:$i,B:$i,A:$i]:
% 1.51/1.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.51/1.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.51/1.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.51/1.75  thf(zf_stmt_5, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.51/1.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.51/1.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.51/1.75  thf('13', plain,
% 1.51/1.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.51/1.75         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.51/1.75          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.51/1.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.75  thf('14', plain,
% 1.51/1.75      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.75      inference('sup-', [status(thm)], ['12', '13'])).
% 1.51/1.75  thf('15', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.51/1.75          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.51/1.75      inference('sup-', [status(thm)], ['11', '14'])).
% 1.51/1.75  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('17', plain,
% 1.51/1.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.51/1.75         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 1.51/1.75          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 1.51/1.75          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.75  thf('18', plain,
% 1.51/1.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.51/1.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['16', '17'])).
% 1.51/1.75  thf('19', plain,
% 1.51/1.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.75  thf('20', plain,
% 1.51/1.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.51/1.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.51/1.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.51/1.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.75  thf('21', plain,
% 1.51/1.75      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.51/1.75      inference('sup-', [status(thm)], ['19', '20'])).
% 1.51/1.75  thf('22', plain,
% 1.51/1.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.75      inference('demod', [status(thm)], ['18', '21'])).
% 1.51/1.75  thf('23', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.51/1.75          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['15', '22'])).
% 1.51/1.75  thf('24', plain,
% 1.51/1.75      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf('25', plain,
% 1.51/1.75      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.51/1.75         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['23', '24'])).
% 1.51/1.75  thf('26', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.75           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.51/1.75           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.51/1.75           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['10', '25'])).
% 1.51/1.75  thf('27', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          (~ (v1_relat_1 @ sk_C)
% 1.51/1.75           | ~ (v1_funct_1 @ sk_C)
% 1.51/1.75           | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.51/1.75           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.51/1.75           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['4', '26'])).
% 1.51/1.75  thf('28', plain,
% 1.51/1.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(cc2_relat_1, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( v1_relat_1 @ A ) =>
% 1.51/1.75       ( ![B:$i]:
% 1.51/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.51/1.75  thf('29', plain,
% 1.51/1.75      (![X10 : $i, X11 : $i]:
% 1.51/1.75         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.51/1.75          | (v1_relat_1 @ X10)
% 1.51/1.75          | ~ (v1_relat_1 @ X11))),
% 1.51/1.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.51/1.75  thf('30', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.51/1.75      inference('sup-', [status(thm)], ['28', '29'])).
% 1.51/1.75  thf(fc6_relat_1, axiom,
% 1.51/1.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.51/1.75  thf('31', plain,
% 1.51/1.75      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 1.51/1.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.51/1.75  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('34', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          (((sk_A) = (k1_relat_1 @ sk_C))
% 1.51/1.75           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.51/1.75           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('demod', [status(thm)], ['27', '32', '33'])).
% 1.51/1.75  thf('35', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          (~ (v1_relat_1 @ sk_C)
% 1.51/1.75           | ~ (v1_funct_1 @ sk_C)
% 1.51/1.75           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.51/1.75           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['3', '34'])).
% 1.51/1.75  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('38', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.51/1.75           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.51/1.75  thf('39', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 1.51/1.75           | ~ (v1_relat_1 @ sk_C)
% 1.51/1.75           | ~ (v1_funct_1 @ sk_C)
% 1.51/1.75           | ~ (v2_funct_1 @ sk_C)
% 1.51/1.75           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup+', [status(thm)], ['2', '38'])).
% 1.51/1.75  thf('40', plain,
% 1.51/1.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(redefinition_k2_relset_1, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.51/1.75  thf('41', plain,
% 1.51/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.51/1.75         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.51/1.75          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.51/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.75  thf('42', plain,
% 1.51/1.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.51/1.75      inference('sup-', [status(thm)], ['40', '41'])).
% 1.51/1.75  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.51/1.75      inference('sup+', [status(thm)], ['42', '43'])).
% 1.51/1.75  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('48', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('demod', [status(thm)], ['39', '44', '45', '46', '47'])).
% 1.51/1.75  thf('49', plain,
% 1.51/1.75      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.75      inference('sup-', [status(thm)], ['12', '13'])).
% 1.51/1.75  thf('50', plain,
% 1.51/1.75      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['48', '49'])).
% 1.51/1.75  thf('51', plain,
% 1.51/1.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.75      inference('demod', [status(thm)], ['18', '21'])).
% 1.51/1.75  thf('52', plain,
% 1.51/1.75      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('clc', [status(thm)], ['50', '51'])).
% 1.51/1.75  thf('53', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf('54', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('55', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('56', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf('57', plain,
% 1.51/1.75      (![X30 : $i]:
% 1.51/1.75         ((m1_subset_1 @ X30 @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 1.51/1.75          | ~ (v1_funct_1 @ X30)
% 1.51/1.75          | ~ (v1_relat_1 @ X30))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.51/1.75  thf('58', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['56', '57'])).
% 1.51/1.75  thf('59', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75             (k1_zfmisc_1 @ 
% 1.51/1.75              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.51/1.75               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['55', '58'])).
% 1.51/1.75  thf('60', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['59'])).
% 1.51/1.75  thf('61', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75             (k1_zfmisc_1 @ 
% 1.51/1.75              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.51/1.75               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['54', '60'])).
% 1.51/1.75  thf('62', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['61'])).
% 1.51/1.75  thf('63', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0))),
% 1.51/1.75      inference('sup+', [status(thm)], ['53', '62'])).
% 1.51/1.75  thf('64', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75             (k1_zfmisc_1 @ 
% 1.51/1.75              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.51/1.75      inference('simplify', [status(thm)], ['63'])).
% 1.51/1.75  thf('65', plain,
% 1.51/1.75      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 1.51/1.75         | ~ (v1_relat_1 @ sk_C)
% 1.51/1.75         | ~ (v1_funct_1 @ sk_C)
% 1.51/1.75         | ~ (v2_funct_1 @ sk_C)))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('sup+', [status(thm)], ['52', '64'])).
% 1.51/1.75  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.51/1.75      inference('sup+', [status(thm)], ['42', '43'])).
% 1.51/1.75  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('70', plain,
% 1.51/1.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.51/1.75  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('72', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('73', plain,
% 1.51/1.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf('74', plain,
% 1.51/1.75      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.75  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('76', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.51/1.75      inference('demod', [status(thm)], ['74', '75'])).
% 1.51/1.75  thf('77', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['71', '76'])).
% 1.51/1.75  thf('78', plain,
% 1.51/1.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf('79', plain,
% 1.51/1.75      (![X22 : $i, X23 : $i]:
% 1.51/1.75         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.75  thf('80', plain,
% 1.51/1.75      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.75      inference('sup-', [status(thm)], ['12', '13'])).
% 1.51/1.75  thf('81', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.51/1.75      inference('sup-', [status(thm)], ['79', '80'])).
% 1.51/1.75  thf('82', plain,
% 1.51/1.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.75      inference('demod', [status(thm)], ['18', '21'])).
% 1.51/1.75  thf('83', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['81', '82'])).
% 1.51/1.75  thf('84', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf('85', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('86', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.51/1.75          | ~ (v1_funct_1 @ X14)
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.75  thf('87', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf('88', plain,
% 1.51/1.75      (![X30 : $i]:
% 1.51/1.75         ((v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))
% 1.51/1.75          | ~ (v1_funct_1 @ X30)
% 1.51/1.75          | ~ (v1_relat_1 @ X30))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.51/1.75  thf('89', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['87', '88'])).
% 1.51/1.75  thf('90', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['86', '89'])).
% 1.51/1.75  thf('91', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['90'])).
% 1.51/1.75  thf('92', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.51/1.75      inference('sup-', [status(thm)], ['85', '91'])).
% 1.51/1.75  thf('93', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['92'])).
% 1.51/1.75  thf('94', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75           (k1_relat_1 @ X0))
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v2_funct_1 @ X0))),
% 1.51/1.75      inference('sup+', [status(thm)], ['84', '93'])).
% 1.51/1.75  thf('95', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0)
% 1.51/1.75          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.51/1.75             (k1_relat_1 @ X0)))),
% 1.51/1.75      inference('simplify', [status(thm)], ['94'])).
% 1.51/1.75  thf('96', plain,
% 1.51/1.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.51/1.75        | ((sk_B) = (k1_xboole_0))
% 1.51/1.75        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.75        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.75        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.75      inference('sup+', [status(thm)], ['83', '95'])).
% 1.51/1.75  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.51/1.75      inference('sup+', [status(thm)], ['42', '43'])).
% 1.51/1.75  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.75      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.75  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('101', plain,
% 1.51/1.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.51/1.75        | ((sk_B) = (k1_xboole_0)))),
% 1.51/1.75      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 1.51/1.75  thf('102', plain,
% 1.51/1.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf('103', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.75  thf('104', plain,
% 1.51/1.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['78', '103'])).
% 1.51/1.75  thf('105', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.75  thf('106', plain,
% 1.51/1.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(t3_subset, axiom,
% 1.51/1.75    (![A:$i,B:$i]:
% 1.51/1.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.75  thf('107', plain,
% 1.51/1.75      (![X7 : $i, X8 : $i]:
% 1.51/1.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.75  thf('108', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['106', '107'])).
% 1.51/1.75  thf(d10_xboole_0, axiom,
% 1.51/1.75    (![A:$i,B:$i]:
% 1.51/1.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.75  thf('109', plain,
% 1.51/1.75      (![X0 : $i, X2 : $i]:
% 1.51/1.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.75  thf('110', plain,
% 1.51/1.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 1.51/1.75        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['108', '109'])).
% 1.51/1.75  thf('111', plain,
% 1.51/1.75      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 1.51/1.75         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['105', '110'])).
% 1.51/1.75  thf('112', plain,
% 1.51/1.75      (![X5 : $i, X6 : $i]:
% 1.51/1.75         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.51/1.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.51/1.75  thf('113', plain,
% 1.51/1.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['112'])).
% 1.51/1.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.51/1.75  thf('114', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.51/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.51/1.75  thf('115', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.75  thf('116', plain,
% 1.51/1.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['112'])).
% 1.51/1.75  thf('117', plain,
% 1.51/1.75      ((((k1_xboole_0) = (sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['111', '113', '114', '115', '116'])).
% 1.51/1.75  thf('118', plain,
% 1.51/1.75      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['104', '117'])).
% 1.51/1.75  thf('119', plain,
% 1.51/1.75      ((((k1_xboole_0) = (sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['111', '113', '114', '115', '116'])).
% 1.51/1.75  thf('120', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('121', plain,
% 1.51/1.75      ((((k2_relset_1 @ sk_A @ sk_B @ k1_xboole_0) = (sk_B)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['119', '120'])).
% 1.51/1.75  thf('122', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.75  thf('123', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.51/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.51/1.75  thf('124', plain,
% 1.51/1.75      (![X7 : $i, X9 : $i]:
% 1.51/1.75         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.75  thf('125', plain,
% 1.51/1.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['123', '124'])).
% 1.51/1.75  thf('126', plain,
% 1.51/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.51/1.75         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.51/1.75          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.51/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.75  thf('127', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['125', '126'])).
% 1.51/1.75  thf('128', plain,
% 1.51/1.75      ((((sk_B) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.75  thf('129', plain,
% 1.51/1.75      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['121', '122', '127', '128'])).
% 1.51/1.75  thf('130', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.75           (k1_zfmisc_1 @ 
% 1.51/1.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.51/1.75          | ~ (v2_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_funct_1 @ X0)
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['61'])).
% 1.51/1.75  thf('131', plain,
% 1.51/1.75      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 1.51/1.75          (k1_zfmisc_1 @ 
% 1.51/1.75           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 1.51/1.75            (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 1.51/1.75         | ~ (v1_relat_1 @ k1_xboole_0)
% 1.51/1.75         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.51/1.75         | ~ (v2_funct_1 @ k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['129', '130'])).
% 1.51/1.75  thf('132', plain,
% 1.51/1.75      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['6'])).
% 1.51/1.75  thf('133', plain,
% 1.51/1.75      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.51/1.75      inference('simplify', [status(thm)], ['6'])).
% 1.51/1.75  thf('134', plain,
% 1.51/1.75      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 1.51/1.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.51/1.75  thf('135', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.51/1.75      inference('sup+', [status(thm)], ['133', '134'])).
% 1.51/1.75  thf('136', plain,
% 1.51/1.75      ((((k1_xboole_0) = (sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['111', '113', '114', '115', '116'])).
% 1.51/1.75  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('138', plain,
% 1.51/1.75      (((v1_funct_1 @ k1_xboole_0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['136', '137'])).
% 1.51/1.75  thf('139', plain,
% 1.51/1.75      ((((k1_xboole_0) = (sk_C)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['111', '113', '114', '115', '116'])).
% 1.51/1.75  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('141', plain,
% 1.51/1.75      (((v2_funct_1 @ k1_xboole_0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['139', '140'])).
% 1.51/1.75  thf('142', plain,
% 1.51/1.75      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['131', '132', '135', '138', '141'])).
% 1.51/1.75  thf('143', plain,
% 1.51/1.75      (![X7 : $i, X8 : $i]:
% 1.51/1.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.51/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.75  thf('144', plain,
% 1.51/1.75      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['142', '143'])).
% 1.51/1.75  thf('145', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.51/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.51/1.75  thf('146', plain,
% 1.51/1.75      (![X0 : $i, X2 : $i]:
% 1.51/1.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.75  thf('147', plain,
% 1.51/1.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['145', '146'])).
% 1.51/1.75  thf('148', plain,
% 1.51/1.75      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['144', '147'])).
% 1.51/1.75  thf('149', plain,
% 1.51/1.75      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['118', '148'])).
% 1.51/1.75  thf('150', plain,
% 1.51/1.75      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['144', '147'])).
% 1.51/1.75  thf('151', plain,
% 1.51/1.75      (![X15 : $i]:
% 1.51/1.75         (~ (v2_funct_1 @ X15)
% 1.51/1.75          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.51/1.75          | ~ (v1_funct_1 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X15))),
% 1.51/1.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.75  thf('152', plain,
% 1.51/1.75      (((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 1.51/1.75         | ~ (v1_relat_1 @ k1_xboole_0)
% 1.51/1.75         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.51/1.75         | ~ (v2_funct_1 @ k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['150', '151'])).
% 1.51/1.75  thf('153', plain,
% 1.51/1.75      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['121', '122', '127', '128'])).
% 1.51/1.75  thf('154', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.51/1.75      inference('sup+', [status(thm)], ['133', '134'])).
% 1.51/1.75  thf('155', plain,
% 1.51/1.75      (((v1_funct_1 @ k1_xboole_0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['136', '137'])).
% 1.51/1.75  thf('156', plain,
% 1.51/1.75      (((v2_funct_1 @ k1_xboole_0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup+', [status(thm)], ['139', '140'])).
% 1.51/1.75  thf('157', plain,
% 1.51/1.75      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 1.51/1.75  thf('158', plain,
% 1.51/1.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['123', '124'])).
% 1.51/1.75  thf('159', plain,
% 1.51/1.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.51/1.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.51/1.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.51/1.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.75  thf('160', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['158', '159'])).
% 1.51/1.75  thf('161', plain,
% 1.51/1.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.51/1.75         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 1.51/1.75          | (v1_funct_2 @ X26 @ X24 @ X25)
% 1.51/1.75          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.75  thf('162', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 1.51/1.75          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.51/1.75          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['160', '161'])).
% 1.51/1.75  thf('163', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.51/1.75          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 1.51/1.75      inference('simplify', [status(thm)], ['162'])).
% 1.51/1.75  thf('164', plain,
% 1.51/1.75      ((![X0 : $i]:
% 1.51/1.75          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.51/1.75           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['157', '163'])).
% 1.51/1.75  thf('165', plain,
% 1.51/1.75      (![X22 : $i, X23 : $i]:
% 1.51/1.75         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.75  thf('166', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 1.51/1.75      inference('simplify', [status(thm)], ['165'])).
% 1.51/1.75  thf('167', plain,
% 1.51/1.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['123', '124'])).
% 1.51/1.75  thf('168', plain,
% 1.51/1.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.51/1.75         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.51/1.75          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.51/1.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.75  thf('169', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.51/1.75      inference('sup-', [status(thm)], ['167', '168'])).
% 1.51/1.75  thf('170', plain,
% 1.51/1.75      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.51/1.75      inference('sup-', [status(thm)], ['166', '169'])).
% 1.51/1.75  thf('171', plain,
% 1.51/1.75      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 1.51/1.75  thf('172', plain,
% 1.51/1.75      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.51/1.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.51/1.75      inference('demod', [status(thm)], ['164', '170', '171'])).
% 1.51/1.75  thf('173', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.51/1.75      inference('demod', [status(thm)], ['149', '172'])).
% 1.51/1.75  thf('174', plain,
% 1.51/1.75      (~
% 1.51/1.75       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.51/1.75       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.51/1.75       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.51/1.75      inference('split', [status(esa)], ['0'])).
% 1.51/1.75  thf('175', plain,
% 1.51/1.75      (~
% 1.51/1.75       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.75      inference('sat_resolution*', [status(thm)], ['77', '173', '174'])).
% 1.51/1.75  thf('176', plain,
% 1.51/1.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.75      inference('simpl_trail', [status(thm)], ['70', '175'])).
% 1.51/1.75  thf('177', plain,
% 1.51/1.75      (($false)
% 1.51/1.75         <= (~
% 1.51/1.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.51/1.75      inference('demod', [status(thm)], ['1', '176'])).
% 1.51/1.75  thf('178', plain,
% 1.51/1.75      (~
% 1.51/1.75       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.51/1.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.51/1.75      inference('sat_resolution*', [status(thm)], ['77', '173', '174'])).
% 1.51/1.75  thf('179', plain, ($false),
% 1.51/1.75      inference('simpl_trail', [status(thm)], ['177', '178'])).
% 1.51/1.75  
% 1.51/1.75  % SZS output end Refutation
% 1.51/1.75  
% 1.51/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
