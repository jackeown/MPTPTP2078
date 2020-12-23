%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlSnVRRihs

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:40 EST 2020

% Result     : Theorem 4.23s
% Output     : Refutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :  158 (1141 expanded)
%              Number of leaves         :   32 ( 334 expanded)
%              Depth                    :   24
%              Number of atoms          : 1387 (18785 expanded)
%              Number of equality atoms :   76 ( 770 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32','35','36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('59',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('62',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('63',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['58','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['57','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','83'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','84','85'])).

thf('87',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['41','86'])).

thf('88',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','84','85'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('103',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('104',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','84','85'])).

thf('111',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('115',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('116',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','84','85'])).

thf('117',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('120',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['87','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlSnVRRihs
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.23/4.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.23/4.42  % Solved by: fo/fo7.sh
% 4.23/4.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.23/4.42  % done 2243 iterations in 3.955s
% 4.23/4.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.23/4.42  % SZS output start Refutation
% 4.23/4.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.23/4.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.23/4.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.23/4.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.23/4.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.23/4.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.23/4.42  thf(sk_B_type, type, sk_B: $i).
% 4.23/4.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.23/4.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.23/4.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.23/4.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.23/4.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.23/4.42  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.23/4.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.23/4.42  thf(sk_A_type, type, sk_A: $i).
% 4.23/4.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.23/4.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.23/4.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.23/4.42  thf(t31_funct_2, conjecture,
% 4.23/4.42    (![A:$i,B:$i,C:$i]:
% 4.23/4.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.23/4.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.23/4.42       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.23/4.42         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.23/4.42           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.23/4.42           ( m1_subset_1 @
% 4.23/4.42             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.23/4.42  thf(zf_stmt_0, negated_conjecture,
% 4.23/4.42    (~( ![A:$i,B:$i,C:$i]:
% 4.23/4.42        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.23/4.42            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.23/4.42          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.23/4.42            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.23/4.42              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.23/4.42              ( m1_subset_1 @
% 4.23/4.42                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 4.23/4.42    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 4.23/4.42  thf('0', plain,
% 4.23/4.42      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 4.23/4.42        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 4.23/4.42        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.23/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.42  thf('1', plain,
% 4.23/4.42      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 4.23/4.42         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.42      inference('split', [status(esa)], ['0'])).
% 4.23/4.42  thf(d1_funct_2, axiom,
% 4.23/4.42    (![A:$i,B:$i,C:$i]:
% 4.23/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.23/4.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.23/4.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.23/4.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.23/4.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.23/4.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.23/4.42  thf(zf_stmt_1, axiom,
% 4.23/4.42    (![B:$i,A:$i]:
% 4.23/4.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.23/4.42       ( zip_tseitin_0 @ B @ A ) ))).
% 4.23/4.42  thf('2', plain,
% 4.23/4.42      (![X22 : $i, X23 : $i]:
% 4.23/4.42         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.23/4.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.23/4.42  thf('3', plain,
% 4.23/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.23/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.42  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.23/4.42  thf(zf_stmt_3, axiom,
% 4.23/4.42    (![C:$i,B:$i,A:$i]:
% 4.23/4.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.23/4.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.23/4.42  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.23/4.42  thf(zf_stmt_5, axiom,
% 4.23/4.42    (![A:$i,B:$i,C:$i]:
% 4.23/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.23/4.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.23/4.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.23/4.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.23/4.42  thf('4', plain,
% 4.23/4.42      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.23/4.42         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.23/4.42          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.23/4.42          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.23/4.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.23/4.42  thf('5', plain,
% 4.23/4.42      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.23/4.42        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.23/4.42      inference('sup-', [status(thm)], ['3', '4'])).
% 4.23/4.42  thf('6', plain,
% 4.23/4.42      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 4.23/4.42      inference('sup-', [status(thm)], ['2', '5'])).
% 4.23/4.42  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.23/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.42  thf('8', plain,
% 4.23/4.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.23/4.42         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 4.23/4.42          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 4.23/4.42          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.23/4.43  thf('9', plain,
% 4.23/4.43      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.23/4.43        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['7', '8'])).
% 4.23/4.43  thf('10', plain,
% 4.23/4.43      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf(redefinition_k1_relset_1, axiom,
% 4.23/4.43    (![A:$i,B:$i,C:$i]:
% 4.23/4.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.43       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.23/4.43  thf('11', plain,
% 4.23/4.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.23/4.43         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 4.23/4.43          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.23/4.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.23/4.43  thf('12', plain,
% 4.23/4.43      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.23/4.43      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.43  thf('13', plain,
% 4.23/4.43      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.23/4.43        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('demod', [status(thm)], ['9', '12'])).
% 4.23/4.43  thf('14', plain,
% 4.23/4.43      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['6', '13'])).
% 4.23/4.43  thf(t55_funct_1, axiom,
% 4.23/4.43    (![A:$i]:
% 4.23/4.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.23/4.43       ( ( v2_funct_1 @ A ) =>
% 4.23/4.43         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.23/4.43           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.23/4.43  thf('15', plain,
% 4.23/4.43      (![X12 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X12)
% 4.23/4.43          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 4.23/4.43          | ~ (v1_funct_1 @ X12)
% 4.23/4.43          | ~ (v1_relat_1 @ X12))),
% 4.23/4.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.23/4.43  thf(dt_k2_funct_1, axiom,
% 4.23/4.43    (![A:$i]:
% 4.23/4.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.23/4.43       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.23/4.43         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.23/4.43  thf('16', plain,
% 4.23/4.43      (![X11 : $i]:
% 4.23/4.43         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 4.23/4.43          | ~ (v1_funct_1 @ X11)
% 4.23/4.43          | ~ (v1_relat_1 @ X11))),
% 4.23/4.43      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.23/4.43  thf('17', plain,
% 4.23/4.43      (![X11 : $i]:
% 4.23/4.43         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 4.23/4.43          | ~ (v1_funct_1 @ X11)
% 4.23/4.43          | ~ (v1_relat_1 @ X11))),
% 4.23/4.43      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.23/4.43  thf('18', plain,
% 4.23/4.43      (![X12 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X12)
% 4.23/4.43          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 4.23/4.43          | ~ (v1_funct_1 @ X12)
% 4.23/4.43          | ~ (v1_relat_1 @ X12))),
% 4.23/4.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.23/4.43  thf(t3_funct_2, axiom,
% 4.23/4.43    (![A:$i]:
% 4.23/4.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.23/4.43       ( ( v1_funct_1 @ A ) & 
% 4.23/4.43         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 4.23/4.43         ( m1_subset_1 @
% 4.23/4.43           A @ 
% 4.23/4.43           ( k1_zfmisc_1 @
% 4.23/4.43             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.23/4.43  thf('19', plain,
% 4.23/4.43      (![X32 : $i]:
% 4.23/4.43         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 4.23/4.43          | ~ (v1_funct_1 @ X32)
% 4.23/4.43          | ~ (v1_relat_1 @ X32))),
% 4.23/4.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.23/4.43  thf('20', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 4.23/4.43      inference('sup+', [status(thm)], ['18', '19'])).
% 4.23/4.43  thf('21', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['17', '20'])).
% 4.23/4.43  thf('22', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['21'])).
% 4.23/4.43  thf('23', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['16', '22'])).
% 4.23/4.43  thf('24', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['23'])).
% 4.23/4.43  thf('25', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43           (k1_relat_1 @ X0))
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0))),
% 4.23/4.43      inference('sup+', [status(thm)], ['15', '24'])).
% 4.23/4.43  thf('26', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.23/4.43             (k1_relat_1 @ X0)))),
% 4.23/4.43      inference('simplify', [status(thm)], ['25'])).
% 4.23/4.43  thf('27', plain,
% 4.23/4.43      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 4.23/4.43        | ((sk_B) = (k1_xboole_0))
% 4.23/4.43        | ~ (v1_relat_1 @ sk_C_1)
% 4.23/4.43        | ~ (v1_funct_1 @ sk_C_1)
% 4.23/4.43        | ~ (v2_funct_1 @ sk_C_1))),
% 4.23/4.43      inference('sup+', [status(thm)], ['14', '26'])).
% 4.23/4.43  thf('28', plain,
% 4.23/4.43      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf(redefinition_k2_relset_1, axiom,
% 4.23/4.43    (![A:$i,B:$i,C:$i]:
% 4.23/4.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.23/4.43  thf('29', plain,
% 4.23/4.43      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.23/4.43         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 4.23/4.43          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.23/4.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.23/4.43  thf('30', plain,
% 4.23/4.43      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 4.23/4.43      inference('sup-', [status(thm)], ['28', '29'])).
% 4.23/4.43  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('32', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 4.23/4.43      inference('sup+', [status(thm)], ['30', '31'])).
% 4.23/4.43  thf('33', plain,
% 4.23/4.43      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf(cc1_relset_1, axiom,
% 4.23/4.43    (![A:$i,B:$i,C:$i]:
% 4.23/4.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.43       ( v1_relat_1 @ C ) ))).
% 4.23/4.43  thf('34', plain,
% 4.23/4.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.23/4.43         ((v1_relat_1 @ X13)
% 4.23/4.43          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 4.23/4.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.23/4.43  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 4.23/4.43      inference('sup-', [status(thm)], ['33', '34'])).
% 4.23/4.43  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('37', plain, ((v2_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('38', plain,
% 4.23/4.43      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 4.23/4.43        | ((sk_B) = (k1_xboole_0)))),
% 4.23/4.43      inference('demod', [status(thm)], ['27', '32', '35', '36', '37'])).
% 4.23/4.43  thf('39', plain,
% 4.23/4.43      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('split', [status(esa)], ['0'])).
% 4.23/4.43  thf('40', plain,
% 4.23/4.43      ((((sk_B) = (k1_xboole_0)))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['38', '39'])).
% 4.23/4.43  thf('41', plain,
% 4.23/4.43      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('demod', [status(thm)], ['1', '40'])).
% 4.23/4.43  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 4.23/4.43      inference('sup-', [status(thm)], ['33', '34'])).
% 4.23/4.43  thf('43', plain,
% 4.23/4.43      (![X11 : $i]:
% 4.23/4.43         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 4.23/4.43          | ~ (v1_funct_1 @ X11)
% 4.23/4.43          | ~ (v1_relat_1 @ X11))),
% 4.23/4.43      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.23/4.43  thf('44', plain,
% 4.23/4.43      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 4.23/4.43         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 4.23/4.43      inference('split', [status(esa)], ['0'])).
% 4.23/4.43  thf('45', plain,
% 4.23/4.43      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 4.23/4.43         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['43', '44'])).
% 4.23/4.43  thf('46', plain, ((v1_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('47', plain,
% 4.23/4.43      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 4.23/4.43      inference('demod', [status(thm)], ['45', '46'])).
% 4.23/4.43  thf('48', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['42', '47'])).
% 4.23/4.43  thf('49', plain,
% 4.23/4.43      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('split', [status(esa)], ['0'])).
% 4.23/4.43  thf('50', plain,
% 4.23/4.43      (![X22 : $i, X23 : $i]:
% 4.23/4.43         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.23/4.43  thf(t113_zfmisc_1, axiom,
% 4.23/4.43    (![A:$i,B:$i]:
% 4.23/4.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.23/4.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.23/4.43  thf('51', plain,
% 4.23/4.43      (![X2 : $i, X3 : $i]:
% 4.23/4.43         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 4.23/4.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.23/4.43  thf('52', plain,
% 4.23/4.43      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['51'])).
% 4.23/4.43  thf('53', plain,
% 4.23/4.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.23/4.43         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.23/4.43      inference('sup+', [status(thm)], ['50', '52'])).
% 4.23/4.43  thf('54', plain,
% 4.23/4.43      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.23/4.43        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.23/4.43      inference('sup-', [status(thm)], ['3', '4'])).
% 4.23/4.43  thf('55', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 4.23/4.43          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 4.23/4.43      inference('sup-', [status(thm)], ['53', '54'])).
% 4.23/4.43  thf('56', plain,
% 4.23/4.43      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 4.23/4.43        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('demod', [status(thm)], ['9', '12'])).
% 4.23/4.43  thf('57', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 4.23/4.43          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['55', '56'])).
% 4.23/4.43  thf('58', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 4.23/4.43      inference('sup+', [status(thm)], ['30', '31'])).
% 4.23/4.43  thf('59', plain,
% 4.23/4.43      (![X12 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X12)
% 4.23/4.43          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 4.23/4.43          | ~ (v1_funct_1 @ X12)
% 4.23/4.43          | ~ (v1_relat_1 @ X12))),
% 4.23/4.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.23/4.43  thf('60', plain,
% 4.23/4.43      (![X11 : $i]:
% 4.23/4.43         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 4.23/4.43          | ~ (v1_funct_1 @ X11)
% 4.23/4.43          | ~ (v1_relat_1 @ X11))),
% 4.23/4.43      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.23/4.43  thf('61', plain,
% 4.23/4.43      (![X11 : $i]:
% 4.23/4.43         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 4.23/4.43          | ~ (v1_funct_1 @ X11)
% 4.23/4.43          | ~ (v1_relat_1 @ X11))),
% 4.23/4.43      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.23/4.43  thf('62', plain,
% 4.23/4.43      (![X12 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X12)
% 4.23/4.43          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 4.23/4.43          | ~ (v1_funct_1 @ X12)
% 4.23/4.43          | ~ (v1_relat_1 @ X12))),
% 4.23/4.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.23/4.43  thf('63', plain,
% 4.23/4.43      (![X32 : $i]:
% 4.23/4.43         ((m1_subset_1 @ X32 @ 
% 4.23/4.43           (k1_zfmisc_1 @ 
% 4.23/4.43            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 4.23/4.43          | ~ (v1_funct_1 @ X32)
% 4.23/4.43          | ~ (v1_relat_1 @ X32))),
% 4.23/4.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.23/4.43  thf('64', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43           (k1_zfmisc_1 @ 
% 4.23/4.43            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 4.23/4.43      inference('sup+', [status(thm)], ['62', '63'])).
% 4.23/4.43  thf('65', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43             (k1_zfmisc_1 @ 
% 4.23/4.43              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 4.23/4.43               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['61', '64'])).
% 4.23/4.43  thf('66', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43           (k1_zfmisc_1 @ 
% 4.23/4.43            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['65'])).
% 4.23/4.43  thf('67', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43             (k1_zfmisc_1 @ 
% 4.23/4.43              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 4.23/4.43               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['60', '66'])).
% 4.23/4.43  thf('68', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43           (k1_zfmisc_1 @ 
% 4.23/4.43            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['67'])).
% 4.23/4.43  thf('69', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v2_funct_1 @ X0))),
% 4.23/4.43      inference('sup+', [status(thm)], ['59', '68'])).
% 4.23/4.43  thf('70', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_funct_1 @ X0)
% 4.23/4.43          | ~ (v1_relat_1 @ X0)
% 4.23/4.43          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.23/4.43             (k1_zfmisc_1 @ 
% 4.23/4.43              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 4.23/4.43      inference('simplify', [status(thm)], ['69'])).
% 4.23/4.43  thf('71', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 4.23/4.43        | ~ (v1_relat_1 @ sk_C_1)
% 4.23/4.43        | ~ (v1_funct_1 @ sk_C_1)
% 4.23/4.43        | ~ (v2_funct_1 @ sk_C_1))),
% 4.23/4.43      inference('sup+', [status(thm)], ['58', '70'])).
% 4.23/4.43  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 4.23/4.43      inference('sup-', [status(thm)], ['33', '34'])).
% 4.23/4.43  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('74', plain, ((v2_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('75', plain,
% 4.23/4.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 4.23/4.43      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 4.23/4.43  thf('76', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.23/4.43        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup+', [status(thm)], ['57', '75'])).
% 4.23/4.43  thf('77', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 4.23/4.43          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['55', '56'])).
% 4.23/4.43  thf('78', plain,
% 4.23/4.43      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('split', [status(esa)], ['0'])).
% 4.23/4.43  thf('79', plain,
% 4.23/4.43      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.23/4.43         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['77', '78'])).
% 4.23/4.43  thf('80', plain,
% 4.23/4.43      (((((sk_A) = (k1_relat_1 @ sk_C_1)) | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('sup-', [status(thm)], ['76', '79'])).
% 4.23/4.43  thf('81', plain,
% 4.23/4.43      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('simplify', [status(thm)], ['80'])).
% 4.23/4.43  thf('82', plain,
% 4.23/4.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 4.23/4.43      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 4.23/4.43  thf('83', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.23/4.43         <= (~
% 4.23/4.43             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.23/4.43      inference('sup+', [status(thm)], ['81', '82'])).
% 4.23/4.43  thf('84', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.23/4.43      inference('demod', [status(thm)], ['49', '83'])).
% 4.23/4.43  thf('85', plain,
% 4.23/4.43      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 4.23/4.43       ~
% 4.23/4.43       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 4.23/4.43       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 4.23/4.43      inference('split', [status(esa)], ['0'])).
% 4.23/4.43  thf('86', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 4.23/4.43      inference('sat_resolution*', [status(thm)], ['48', '84', '85'])).
% 4.23/4.43  thf('87', plain,
% 4.23/4.43      (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)),
% 4.23/4.43      inference('simpl_trail', [status(thm)], ['41', '86'])).
% 4.23/4.43  thf('88', plain,
% 4.23/4.43      (![X12 : $i]:
% 4.23/4.43         (~ (v2_funct_1 @ X12)
% 4.23/4.43          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 4.23/4.43          | ~ (v1_funct_1 @ X12)
% 4.23/4.43          | ~ (v1_relat_1 @ X12))),
% 4.23/4.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.23/4.43  thf('89', plain,
% 4.23/4.43      ((((sk_B) = (k1_xboole_0)))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['38', '39'])).
% 4.23/4.43  thf('90', plain,
% 4.23/4.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 4.23/4.43      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 4.23/4.43  thf('91', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 4.23/4.43         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k1_relat_1 @ sk_C_1)))))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('sup+', [status(thm)], ['89', '90'])).
% 4.23/4.43  thf('92', plain,
% 4.23/4.43      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['51'])).
% 4.23/4.43  thf('93', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('demod', [status(thm)], ['91', '92'])).
% 4.23/4.43  thf('94', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 4.23/4.43      inference('sat_resolution*', [status(thm)], ['48', '84', '85'])).
% 4.23/4.43  thf('95', plain,
% 4.23/4.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.23/4.43      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 4.23/4.43  thf('96', plain,
% 4.23/4.43      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['51'])).
% 4.23/4.43  thf('97', plain,
% 4.23/4.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.23/4.43         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 4.23/4.43          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.23/4.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.23/4.43  thf('98', plain,
% 4.23/4.43      (![X0 : $i, X1 : $i]:
% 4.23/4.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.23/4.43          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['96', '97'])).
% 4.23/4.43  thf('99', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         ((k1_relset_1 @ k1_xboole_0 @ X0 @ (k2_funct_1 @ sk_C_1))
% 4.23/4.43           = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['95', '98'])).
% 4.23/4.43  thf('100', plain,
% 4.23/4.43      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.23/4.43         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 4.23/4.43          | (v1_funct_2 @ X26 @ X24 @ X25)
% 4.23/4.43          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.23/4.43  thf('101', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k1_xboole_0) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 4.23/4.43          | ~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ k1_xboole_0)
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ X0))),
% 4.23/4.43      inference('sup-', [status(thm)], ['99', '100'])).
% 4.23/4.43  thf('102', plain,
% 4.23/4.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('demod', [status(thm)], ['91', '92'])).
% 4.23/4.43  thf('103', plain,
% 4.23/4.43      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.23/4.43      inference('simplify', [status(thm)], ['51'])).
% 4.23/4.43  thf('104', plain,
% 4.23/4.43      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.23/4.43         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.23/4.43          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.23/4.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.23/4.43  thf('105', plain,
% 4.23/4.43      (![X0 : $i, X1 : $i]:
% 4.23/4.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.23/4.43          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 4.23/4.43          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 4.23/4.43      inference('sup-', [status(thm)], ['103', '104'])).
% 4.23/4.43  thf('106', plain,
% 4.23/4.43      (![X22 : $i, X23 : $i]:
% 4.23/4.43         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.23/4.43  thf('107', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 4.23/4.43      inference('simplify', [status(thm)], ['106'])).
% 4.23/4.43  thf('108', plain,
% 4.23/4.43      (![X0 : $i, X1 : $i]:
% 4.23/4.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.23/4.43          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 4.23/4.43      inference('demod', [status(thm)], ['105', '107'])).
% 4.23/4.43  thf('109', plain,
% 4.23/4.43      ((![X0 : $i]: (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ k1_xboole_0))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['102', '108'])).
% 4.23/4.43  thf('110', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 4.23/4.43      inference('sat_resolution*', [status(thm)], ['48', '84', '85'])).
% 4.23/4.43  thf('111', plain,
% 4.23/4.43      (![X0 : $i]: (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ k1_xboole_0)),
% 4.23/4.43      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 4.23/4.43  thf('112', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k1_xboole_0) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ X0))),
% 4.23/4.43      inference('demod', [status(thm)], ['101', '111'])).
% 4.23/4.43  thf('113', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k1_xboole_0) != (k2_relat_1 @ sk_C_1))
% 4.23/4.43          | ~ (v1_relat_1 @ sk_C_1)
% 4.23/4.43          | ~ (v1_funct_1 @ sk_C_1)
% 4.23/4.43          | ~ (v2_funct_1 @ sk_C_1)
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ X0))),
% 4.23/4.43      inference('sup-', [status(thm)], ['88', '112'])).
% 4.23/4.43  thf('114', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 4.23/4.43      inference('sup+', [status(thm)], ['30', '31'])).
% 4.23/4.43  thf('115', plain,
% 4.23/4.43      ((((sk_B) = (k1_xboole_0)))
% 4.23/4.43         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 4.23/4.43      inference('sup-', [status(thm)], ['38', '39'])).
% 4.23/4.43  thf('116', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 4.23/4.43      inference('sat_resolution*', [status(thm)], ['48', '84', '85'])).
% 4.23/4.43  thf('117', plain, (((sk_B) = (k1_xboole_0))),
% 4.23/4.43      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 4.23/4.43  thf('118', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 4.23/4.43      inference('demod', [status(thm)], ['114', '117'])).
% 4.23/4.43  thf('119', plain, ((v1_relat_1 @ sk_C_1)),
% 4.23/4.43      inference('sup-', [status(thm)], ['33', '34'])).
% 4.23/4.43  thf('120', plain, ((v1_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('121', plain, ((v2_funct_1 @ sk_C_1)),
% 4.23/4.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.43  thf('122', plain,
% 4.23/4.43      (![X0 : $i]:
% 4.23/4.43         (((k1_xboole_0) != (k1_xboole_0))
% 4.23/4.43          | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ X0))),
% 4.23/4.43      inference('demod', [status(thm)], ['113', '118', '119', '120', '121'])).
% 4.23/4.43  thf('123', plain,
% 4.23/4.43      (![X0 : $i]: (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ X0)),
% 4.23/4.43      inference('simplify', [status(thm)], ['122'])).
% 4.23/4.43  thf('124', plain, ($false), inference('demod', [status(thm)], ['87', '123'])).
% 4.23/4.43  
% 4.23/4.43  % SZS output end Refutation
% 4.23/4.43  
% 4.23/4.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
