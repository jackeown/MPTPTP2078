%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4fSyTZcgMl

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:48 EST 2020

% Result     : Theorem 19.36s
% Output     : Refutation 19.36s
% Verified   : 
% Statistics : Number of formulae       :  384 (5446 expanded)
%              Number of leaves         :   40 (1591 expanded)
%              Depth                    :   81
%              Number of atoms          : 4040 (81274 expanded)
%              Number of equality atoms :  143 (2666 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
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

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','92','93','94','95'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('101',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('109',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('111',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('113',plain,(
    ! [X27: $i] :
      ( ( v1_funct_2 @ X27 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','128'])).

thf('130',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('133',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('137',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('139',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('142',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('144',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('145',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('147',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('148',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('150',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('165',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['162','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('184',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('185',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('186',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['183','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['132','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['131','213'])).

thf('215',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('216',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['214','216'])).

thf('218',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('219',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('220',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('223',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['223','224','225','226'])).

thf('228',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('229',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['220','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('235',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['219','235'])).

thf('237',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('238',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241'])).

thf('243',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('244',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('245',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('246',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['244','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['243','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['242','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('257',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['218','259'])).

thf('261',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['217','260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('263',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['261','262'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('264',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('265',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('266',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['263','264','265','266','267'])).

thf('269',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('271',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( v1_funct_2 @ X28 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['269','272'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('274',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('275',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241'])).

thf('276',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('277',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('278',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('279',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['277','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('284',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['282','283','284','285'])).

thf('287',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('288',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('290',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('294',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['273','274','275','276','290','291','292','293'])).

thf('295',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','294'])).

thf('296',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('297',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['129','298'])).

thf('300',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('301',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['106','299','300'])).

thf('302',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['99','301'])).

thf('303',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('304',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('305',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('306',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['106','299','300'])).

thf('307',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['305','306'])).

thf('308',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['304','307'])).

thf('309',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('310',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('312',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('313',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['311','312'])).

thf('314',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['106','299','300'])).

thf('315',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['313','314'])).

thf('316',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['310','315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('318',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['316','317'])).

thf('319',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('320',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['318','319','320','321','322'])).

thf('324',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('326',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('327',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['324','327'])).

thf('329',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('330',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241'])).

thf('331',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['305','306'])).

thf('332',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('334',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['328','329','332','333','334','335','336'])).

thf('338',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['303','337'])).

thf('339',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('340',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['338','339','340'])).

thf('342',plain,(
    $false ),
    inference(demod,[status(thm)],['302','341'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4fSyTZcgMl
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.36/19.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.36/19.55  % Solved by: fo/fo7.sh
% 19.36/19.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.36/19.55  % done 10849 iterations in 19.086s
% 19.36/19.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.36/19.55  % SZS output start Refutation
% 19.36/19.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.36/19.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 19.36/19.55  thf(sk_B_type, type, sk_B: $i).
% 19.36/19.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.36/19.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 19.36/19.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.36/19.55  thf(sk_C_type, type, sk_C: $i).
% 19.36/19.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 19.36/19.55  thf(sk_A_type, type, sk_A: $i).
% 19.36/19.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.36/19.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.36/19.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.36/19.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 19.36/19.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.36/19.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.36/19.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 19.36/19.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.36/19.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.36/19.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.36/19.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 19.36/19.55  thf(t31_funct_2, conjecture,
% 19.36/19.55    (![A:$i,B:$i,C:$i]:
% 19.36/19.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 19.36/19.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.36/19.55       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 19.36/19.55         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 19.36/19.55           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 19.36/19.55           ( m1_subset_1 @
% 19.36/19.55             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 19.36/19.55  thf(zf_stmt_0, negated_conjecture,
% 19.36/19.55    (~( ![A:$i,B:$i,C:$i]:
% 19.36/19.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 19.36/19.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.36/19.55          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 19.36/19.55            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 19.36/19.55              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 19.36/19.55              ( m1_subset_1 @
% 19.36/19.55                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 19.36/19.55    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 19.36/19.55  thf('0', plain,
% 19.36/19.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 19.36/19.55        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('1', plain,
% 19.36/19.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf(d1_funct_2, axiom,
% 19.36/19.55    (![A:$i,B:$i,C:$i]:
% 19.36/19.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.36/19.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.36/19.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 19.36/19.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 19.36/19.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.36/19.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 19.36/19.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 19.36/19.55  thf(zf_stmt_1, axiom,
% 19.36/19.55    (![B:$i,A:$i]:
% 19.36/19.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.36/19.55       ( zip_tseitin_0 @ B @ A ) ))).
% 19.36/19.55  thf('2', plain,
% 19.36/19.55      (![X19 : $i, X20 : $i]:
% 19.36/19.55         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.36/19.55  thf('3', plain,
% 19.36/19.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.36/19.55  thf(zf_stmt_3, axiom,
% 19.36/19.55    (![C:$i,B:$i,A:$i]:
% 19.36/19.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.36/19.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 19.36/19.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 19.36/19.55  thf(zf_stmt_5, axiom,
% 19.36/19.55    (![A:$i,B:$i,C:$i]:
% 19.36/19.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.36/19.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.36/19.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.36/19.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 19.36/19.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 19.36/19.55  thf('4', plain,
% 19.36/19.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 19.36/19.55         (~ (zip_tseitin_0 @ X24 @ X25)
% 19.36/19.55          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 19.36/19.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.36/19.55  thf('5', plain,
% 19.36/19.55      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 19.36/19.55      inference('sup-', [status(thm)], ['3', '4'])).
% 19.36/19.55  thf('6', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 19.36/19.55      inference('sup-', [status(thm)], ['2', '5'])).
% 19.36/19.55  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('8', plain,
% 19.36/19.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 19.36/19.55         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 19.36/19.55          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 19.36/19.55          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.36/19.55  thf('9', plain,
% 19.36/19.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 19.36/19.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['7', '8'])).
% 19.36/19.55  thf('10', plain,
% 19.36/19.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf(redefinition_k1_relset_1, axiom,
% 19.36/19.55    (![A:$i,B:$i,C:$i]:
% 19.36/19.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.36/19.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 19.36/19.55  thf('11', plain,
% 19.36/19.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.36/19.55         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 19.36/19.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 19.36/19.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.36/19.55  thf('12', plain,
% 19.36/19.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 19.36/19.55      inference('sup-', [status(thm)], ['10', '11'])).
% 19.36/19.55  thf('13', plain,
% 19.36/19.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)], ['9', '12'])).
% 19.36/19.55  thf('14', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['6', '13'])).
% 19.36/19.55  thf(t55_funct_1, axiom,
% 19.36/19.55    (![A:$i]:
% 19.36/19.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.36/19.55       ( ( v2_funct_1 @ A ) =>
% 19.36/19.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 19.36/19.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 19.36/19.55  thf('15', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('16', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['6', '13'])).
% 19.36/19.55  thf(fc6_funct_1, axiom,
% 19.36/19.55    (![A:$i]:
% 19.36/19.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 19.36/19.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 19.36/19.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 19.36/19.55         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 19.36/19.55  thf('17', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf(dt_k2_funct_1, axiom,
% 19.36/19.55    (![A:$i]:
% 19.36/19.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.36/19.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 19.36/19.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 19.36/19.55  thf('18', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('19', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('20', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('21', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('22', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('23', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('24', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('25', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('26', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('27', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('28', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('29', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf(d10_xboole_0, axiom,
% 19.36/19.55    (![A:$i,B:$i]:
% 19.36/19.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.36/19.55  thf('30', plain,
% 19.36/19.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 19.36/19.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.55  thf('31', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 19.36/19.55      inference('simplify', [status(thm)], ['30'])).
% 19.36/19.55  thf(d18_relat_1, axiom,
% 19.36/19.55    (![A:$i,B:$i]:
% 19.36/19.55     ( ( v1_relat_1 @ B ) =>
% 19.36/19.55       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 19.36/19.55  thf('32', plain,
% 19.36/19.55      (![X6 : $i, X7 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 19.36/19.55          | (v4_relat_1 @ X6 @ X7)
% 19.36/19.55          | ~ (v1_relat_1 @ X6))),
% 19.36/19.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 19.36/19.55  thf('33', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['31', '32'])).
% 19.36/19.55  thf('34', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['29', '33'])).
% 19.36/19.55  thf('35', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['28', '34'])).
% 19.36/19.55  thf('36', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['35'])).
% 19.36/19.55  thf('37', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['27', '36'])).
% 19.36/19.55  thf('38', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['26', '37'])).
% 19.36/19.55  thf('39', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['38'])).
% 19.36/19.55  thf('40', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['25', '39'])).
% 19.36/19.55  thf('41', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['40'])).
% 19.36/19.55  thf('42', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['24', '41'])).
% 19.36/19.55  thf('43', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['42'])).
% 19.36/19.55  thf('44', plain,
% 19.36/19.55      (![X6 : $i, X7 : $i]:
% 19.36/19.55         (~ (v4_relat_1 @ X6 @ X7)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 19.36/19.55          | ~ (v1_relat_1 @ X6))),
% 19.36/19.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 19.36/19.55  thf('45', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['43', '44'])).
% 19.36/19.55  thf('46', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('sup-', [status(thm)], ['23', '45'])).
% 19.36/19.55  thf('47', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['22', '46'])).
% 19.36/19.55  thf('48', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['47'])).
% 19.36/19.55  thf('49', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['21', '48'])).
% 19.36/19.55  thf('50', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['49'])).
% 19.36/19.55  thf('51', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0))),
% 19.36/19.55      inference('sup+', [status(thm)], ['20', '50'])).
% 19.36/19.55  thf('52', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['19', '51'])).
% 19.36/19.55  thf('53', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['52'])).
% 19.36/19.55  thf('54', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['18', '53'])).
% 19.36/19.55  thf('55', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['54'])).
% 19.36/19.55  thf('56', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['17', '55'])).
% 19.36/19.55  thf('57', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['56'])).
% 19.36/19.55  thf('58', plain,
% 19.36/19.55      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['16', '57'])).
% 19.36/19.55  thf('59', plain,
% 19.36/19.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf(cc2_relat_1, axiom,
% 19.36/19.55    (![A:$i]:
% 19.36/19.55     ( ( v1_relat_1 @ A ) =>
% 19.36/19.55       ( ![B:$i]:
% 19.36/19.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 19.36/19.55  thf('60', plain,
% 19.36/19.55      (![X4 : $i, X5 : $i]:
% 19.36/19.55         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 19.36/19.55          | (v1_relat_1 @ X4)
% 19.36/19.55          | ~ (v1_relat_1 @ X5))),
% 19.36/19.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.36/19.55  thf('61', plain,
% 19.36/19.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 19.36/19.55      inference('sup-', [status(thm)], ['59', '60'])).
% 19.36/19.55  thf(fc6_relat_1, axiom,
% 19.36/19.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 19.36/19.55  thf('62', plain,
% 19.36/19.55      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.36/19.55  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('66', plain,
% 19.36/19.55      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['58', '63', '64', '65'])).
% 19.36/19.55  thf('67', plain,
% 19.36/19.55      (![X0 : $i, X2 : $i]:
% 19.36/19.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.36/19.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.55  thf('68', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['66', '67'])).
% 19.36/19.55  thf('69', plain,
% 19.36/19.55      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C)
% 19.36/19.55        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['15', '68'])).
% 19.36/19.55  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('73', plain,
% 19.36/19.55      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 19.36/19.55        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 19.36/19.55  thf('74', plain,
% 19.36/19.55      ((~ (r1_tarski @ sk_A @ sk_A)
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['14', '73'])).
% 19.36/19.55  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 19.36/19.55      inference('simplify', [status(thm)], ['30'])).
% 19.36/19.55  thf('76', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('demod', [status(thm)], ['74', '75'])).
% 19.36/19.55  thf('77', plain,
% 19.36/19.55      ((((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['76'])).
% 19.36/19.55  thf('78', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('79', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('80', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf(t3_funct_2, axiom,
% 19.36/19.55    (![A:$i]:
% 19.36/19.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.36/19.55       ( ( v1_funct_1 @ A ) & 
% 19.36/19.55         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 19.36/19.55         ( m1_subset_1 @
% 19.36/19.55           A @ 
% 19.36/19.55           ( k1_zfmisc_1 @
% 19.36/19.55             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 19.36/19.55  thf('81', plain,
% 19.36/19.55      (![X27 : $i]:
% 19.36/19.55         ((m1_subset_1 @ X27 @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))))
% 19.36/19.55          | ~ (v1_funct_1 @ X27)
% 19.36/19.55          | ~ (v1_relat_1 @ X27))),
% 19.36/19.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 19.36/19.55  thf('82', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['80', '81'])).
% 19.36/19.55  thf('83', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 19.36/19.55               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['79', '82'])).
% 19.36/19.55  thf('84', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['83'])).
% 19.36/19.55  thf('85', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 19.36/19.55               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['78', '84'])).
% 19.36/19.55  thf('86', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['85'])).
% 19.36/19.55  thf('87', plain,
% 19.36/19.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['77', '86'])).
% 19.36/19.55  thf('88', plain,
% 19.36/19.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf(redefinition_k2_relset_1, axiom,
% 19.36/19.55    (![A:$i,B:$i,C:$i]:
% 19.36/19.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.36/19.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 19.36/19.55  thf('89', plain,
% 19.36/19.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 19.36/19.55         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 19.36/19.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 19.36/19.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 19.36/19.55  thf('90', plain,
% 19.36/19.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 19.36/19.55      inference('sup-', [status(thm)], ['88', '89'])).
% 19.36/19.55  thf('91', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('96', plain,
% 19.36/19.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['87', '92', '93', '94', '95'])).
% 19.36/19.55  thf('97', plain,
% 19.36/19.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf('98', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['96', '97'])).
% 19.36/19.55  thf('99', plain,
% 19.36/19.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('demod', [status(thm)], ['1', '98'])).
% 19.36/19.55  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('101', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('102', plain,
% 19.36/19.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf('103', plain,
% 19.36/19.55      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 19.36/19.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['101', '102'])).
% 19.36/19.55  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('105', plain,
% 19.36/19.55      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('demod', [status(thm)], ['103', '104'])).
% 19.36/19.55  thf('106', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['100', '105'])).
% 19.36/19.55  thf('107', plain,
% 19.36/19.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf('108', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['6', '13'])).
% 19.36/19.55  thf('109', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('110', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('111', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('112', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('113', plain,
% 19.36/19.55      (![X27 : $i]:
% 19.36/19.55         ((v1_funct_2 @ X27 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))
% 19.36/19.55          | ~ (v1_funct_1 @ X27)
% 19.36/19.55          | ~ (v1_relat_1 @ X27))),
% 19.36/19.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 19.36/19.55  thf('114', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['112', '113'])).
% 19.36/19.55  thf('115', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['111', '114'])).
% 19.36/19.55  thf('116', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['115'])).
% 19.36/19.55  thf('117', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['110', '116'])).
% 19.36/19.55  thf('118', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['117'])).
% 19.36/19.55  thf('119', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0))),
% 19.36/19.55      inference('sup+', [status(thm)], ['109', '118'])).
% 19.36/19.55  thf('120', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['119'])).
% 19.36/19.55  thf('121', plain,
% 19.36/19.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 19.36/19.55        | ((sk_B) = (k1_xboole_0))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['108', '120'])).
% 19.36/19.55  thf('122', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('126', plain,
% 19.36/19.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 19.36/19.55        | ((sk_B) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 19.36/19.55  thf('127', plain,
% 19.36/19.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf('128', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['126', '127'])).
% 19.36/19.55  thf('129', plain,
% 19.36/19.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('demod', [status(thm)], ['107', '128'])).
% 19.36/19.55  thf('130', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('131', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['126', '127'])).
% 19.36/19.55  thf('132', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('133', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('134', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('135', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('136', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('137', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('138', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('139', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('140', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('141', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('142', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('143', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('144', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('145', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('146', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('147', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('148', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('149', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['49'])).
% 19.36/19.55  thf('150', plain,
% 19.36/19.55      (![X0 : $i, X2 : $i]:
% 19.36/19.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.36/19.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.55  thf('151', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 19.36/19.55               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['149', '150'])).
% 19.36/19.55  thf('152', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('sup-', [status(thm)], ['148', '151'])).
% 19.36/19.55  thf('153', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['147', '152'])).
% 19.36/19.55  thf('154', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 19.36/19.55      inference('simplify', [status(thm)], ['30'])).
% 19.36/19.55  thf('155', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['153', '154'])).
% 19.36/19.55  thf('156', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['155'])).
% 19.36/19.55  thf('157', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['146', '156'])).
% 19.36/19.55  thf('158', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['157'])).
% 19.36/19.55  thf('159', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['145', '158'])).
% 19.36/19.55  thf('160', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['159'])).
% 19.36/19.55  thf('161', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k1_relat_1 @ X0)
% 19.36/19.55              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['144', '160'])).
% 19.36/19.55  thf('162', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (((k1_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['161'])).
% 19.36/19.55  thf('163', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('164', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['35'])).
% 19.36/19.55  thf('165', plain,
% 19.36/19.55      (![X6 : $i, X7 : $i]:
% 19.36/19.55         (~ (v4_relat_1 @ X6 @ X7)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 19.36/19.55          | ~ (v1_relat_1 @ X6))),
% 19.36/19.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 19.36/19.55  thf('166', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['164', '165'])).
% 19.36/19.55  thf('167', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('sup-', [status(thm)], ['163', '166'])).
% 19.36/19.55  thf('168', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['167'])).
% 19.36/19.55  thf('169', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['162', '168'])).
% 19.36/19.55  thf('170', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['143', '169'])).
% 19.36/19.55  thf('171', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['170'])).
% 19.36/19.55  thf('172', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['142', '171'])).
% 19.36/19.55  thf('173', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['172'])).
% 19.36/19.55  thf('174', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['141', '173'])).
% 19.36/19.55  thf('175', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['174'])).
% 19.36/19.55  thf('176', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['140', '175'])).
% 19.36/19.55  thf('177', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['139', '176'])).
% 19.36/19.55  thf('178', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['177'])).
% 19.36/19.55  thf('179', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['138', '178'])).
% 19.36/19.55  thf('180', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['179'])).
% 19.36/19.55  thf('181', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['137', '180'])).
% 19.36/19.55  thf('182', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['181'])).
% 19.36/19.55  thf('183', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('184', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('185', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('186', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('187', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['56'])).
% 19.36/19.55  thf('188', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['186', '187'])).
% 19.36/19.55  thf('189', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k2_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['185', '188'])).
% 19.36/19.55  thf('190', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['189'])).
% 19.36/19.55  thf('191', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k2_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['184', '190'])).
% 19.36/19.55  thf('192', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['191'])).
% 19.36/19.55  thf('193', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55             (k2_relat_1 @ X0)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['183', '192'])).
% 19.36/19.55  thf('194', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 19.36/19.55           (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['193'])).
% 19.36/19.55  thf('195', plain,
% 19.36/19.55      (![X0 : $i, X2 : $i]:
% 19.36/19.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.36/19.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.55  thf('196', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 19.36/19.55               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ((k2_relat_1 @ X0)
% 19.36/19.55              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['194', '195'])).
% 19.36/19.55  thf('197', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ((k2_relat_1 @ X0)
% 19.36/19.55              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('sup-', [status(thm)], ['182', '196'])).
% 19.36/19.55  thf('198', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (((k2_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['197'])).
% 19.36/19.55  thf('199', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['85'])).
% 19.36/19.55  thf('200', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['198', '199'])).
% 19.36/19.55  thf('201', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55               (k2_relat_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['136', '200'])).
% 19.36/19.55  thf('202', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['201'])).
% 19.36/19.55  thf('203', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55               (k2_relat_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['135', '202'])).
% 19.36/19.55  thf('204', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['203'])).
% 19.36/19.55  thf('205', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55               (k2_relat_1 @ X0)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['134', '204'])).
% 19.36/19.55  thf('206', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['205'])).
% 19.36/19.55  thf('207', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0))),
% 19.36/19.55      inference('sup+', [status(thm)], ['133', '206'])).
% 19.36/19.55  thf('208', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 19.36/19.55      inference('simplify', [status(thm)], ['207'])).
% 19.36/19.55  thf('209', plain,
% 19.36/19.55      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['132', '208'])).
% 19.36/19.55  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('213', plain,
% 19.36/19.55      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 19.36/19.55      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 19.36/19.55  thf('214', plain,
% 19.36/19.55      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0))))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['131', '213'])).
% 19.36/19.55  thf('215', plain,
% 19.36/19.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 19.36/19.55         (((X24) != (k1_xboole_0))
% 19.36/19.55          | ((X25) = (k1_xboole_0))
% 19.36/19.55          | ((X26) = (k1_xboole_0))
% 19.36/19.55          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 19.36/19.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.36/19.55  thf('216', plain,
% 19.36/19.55      (![X25 : $i, X26 : $i]:
% 19.36/19.55         (~ (m1_subset_1 @ X26 @ 
% 19.36/19.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 19.36/19.55          | ~ (v1_funct_2 @ X26 @ X25 @ k1_xboole_0)
% 19.36/19.55          | ((X26) = (k1_xboole_0))
% 19.36/19.55          | ((X25) = (k1_xboole_0)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['215'])).
% 19.36/19.55  thf('217', plain,
% 19.36/19.55      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55         | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 19.36/19.55         | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55              (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['214', '216'])).
% 19.36/19.55  thf('218', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['126', '127'])).
% 19.36/19.55  thf('219', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('220', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('221', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('222', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['35'])).
% 19.36/19.55  thf('223', plain,
% 19.36/19.55      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['221', '222'])).
% 19.36/19.55  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('227', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 19.36/19.55      inference('demod', [status(thm)], ['223', '224', '225', '226'])).
% 19.36/19.55  thf('228', plain,
% 19.36/19.55      (![X6 : $i, X7 : $i]:
% 19.36/19.55         (~ (v4_relat_1 @ X6 @ X7)
% 19.36/19.55          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 19.36/19.55          | ~ (v1_relat_1 @ X6))),
% 19.36/19.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 19.36/19.55  thf('229', plain,
% 19.36/19.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 19.36/19.55      inference('sup-', [status(thm)], ['227', '228'])).
% 19.36/19.55  thf('230', plain,
% 19.36/19.55      ((~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 19.36/19.55      inference('sup-', [status(thm)], ['220', '229'])).
% 19.36/19.55  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('233', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 19.36/19.55      inference('demod', [status(thm)], ['230', '231', '232'])).
% 19.36/19.55  thf('234', plain,
% 19.36/19.55      (![X0 : $i, X2 : $i]:
% 19.36/19.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.36/19.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.55  thf('235', plain,
% 19.36/19.55      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 19.36/19.55        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['233', '234'])).
% 19.36/19.55  thf('236', plain,
% 19.36/19.55      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C)
% 19.36/19.55        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['219', '235'])).
% 19.36/19.55  thf('237', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('238', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 19.36/19.55      inference('simplify', [status(thm)], ['30'])).
% 19.36/19.55  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('241', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('242', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)],
% 19.36/19.55                ['236', '237', '238', '239', '240', '241'])).
% 19.36/19.55  thf('243', plain,
% 19.36/19.55      (![X11 : $i]:
% 19.36/19.55         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 19.36/19.55          | ~ (v2_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_funct_1 @ X11)
% 19.36/19.55          | ~ (v1_relat_1 @ X11))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 19.36/19.55  thf('244', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('245', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('246', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('247', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.36/19.55             (k1_relat_1 @ X0)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['119'])).
% 19.36/19.55  thf('248', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 19.36/19.55           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['246', '247'])).
% 19.36/19.55  thf('249', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['245', '248'])).
% 19.36/19.55  thf('250', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 19.36/19.55           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['249'])).
% 19.36/19.55  thf('251', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['244', '250'])).
% 19.36/19.55  thf('252', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 19.36/19.55           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['251'])).
% 19.36/19.55  thf('253', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 19.36/19.55             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['243', '252'])).
% 19.36/19.55  thf('254', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 19.36/19.55           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['253'])).
% 19.36/19.55  thf('255', plain,
% 19.36/19.55      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55         (k1_relat_1 @ sk_C) @ sk_B)
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['242', '254'])).
% 19.36/19.55  thf('256', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('257', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('258', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('259', plain,
% 19.36/19.55      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_relat_1 @ sk_C) @ sk_B)),
% 19.36/19.55      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 19.36/19.55  thf('260', plain,
% 19.36/19.55      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55         (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['218', '259'])).
% 19.36/19.55  thf('261', plain,
% 19.36/19.55      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55         | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('demod', [status(thm)], ['217', '260'])).
% 19.36/19.55  thf('262', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (((k1_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['161'])).
% 19.36/19.55  thf('263', plain,
% 19.36/19.55      (((((k1_relat_1 @ sk_C) = (k1_relat_1 @ k1_xboole_0))
% 19.36/19.55         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55         | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55         | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55         | ~ (v2_funct_1 @ sk_C)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup+', [status(thm)], ['261', '262'])).
% 19.36/19.55  thf(t60_relat_1, axiom,
% 19.36/19.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 19.36/19.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 19.36/19.55  thf('264', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.36/19.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.36/19.55  thf('265', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('266', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('267', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('268', plain,
% 19.36/19.55      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('demod', [status(thm)], ['263', '264', '265', '266', '267'])).
% 19.36/19.55  thf('269', plain,
% 19.36/19.55      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['268'])).
% 19.36/19.55  thf('270', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf(t4_funct_2, axiom,
% 19.36/19.55    (![A:$i,B:$i]:
% 19.36/19.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 19.36/19.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 19.36/19.55         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 19.36/19.55           ( m1_subset_1 @
% 19.36/19.55             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 19.36/19.55  thf('271', plain,
% 19.36/19.55      (![X28 : $i, X29 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 19.36/19.55          | (v1_funct_2 @ X28 @ (k1_relat_1 @ X28) @ X29)
% 19.36/19.55          | ~ (v1_funct_1 @ X28)
% 19.36/19.55          | ~ (v1_relat_1 @ X28))),
% 19.36/19.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 19.36/19.55  thf('272', plain,
% 19.36/19.55      (![X0 : $i, X1 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 19.36/19.55      inference('sup-', [status(thm)], ['270', '271'])).
% 19.36/19.55  thf('273', plain,
% 19.36/19.55      ((![X0 : $i]:
% 19.36/19.55          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 19.36/19.55           | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55              (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 19.36/19.55           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55           | ~ (v2_funct_1 @ sk_C)
% 19.36/19.55           | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55           | ~ (v1_relat_1 @ sk_C)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['269', '272'])).
% 19.36/19.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.36/19.55  thf('274', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 19.36/19.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.36/19.55  thf('275', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)],
% 19.36/19.55                ['236', '237', '238', '239', '240', '241'])).
% 19.36/19.55  thf('276', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['126', '127'])).
% 19.36/19.55  thf('277', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 19.36/19.55      inference('sup+', [status(thm)], ['90', '91'])).
% 19.36/19.55  thf('278', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('279', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ 
% 19.36/19.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['85'])).
% 19.36/19.55  thf('280', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0))),
% 19.36/19.55      inference('sup+', [status(thm)], ['278', '279'])).
% 19.36/19.55  thf('281', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 19.36/19.55      inference('simplify', [status(thm)], ['280'])).
% 19.36/19.55  thf('282', plain,
% 19.36/19.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['277', '281'])).
% 19.36/19.55  thf('283', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('284', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('285', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('286', plain,
% 19.36/19.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 19.36/19.55      inference('demod', [status(thm)], ['282', '283', '284', '285'])).
% 19.36/19.55  thf('287', plain,
% 19.36/19.55      (![X4 : $i, X5 : $i]:
% 19.36/19.55         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 19.36/19.55          | (v1_relat_1 @ X4)
% 19.36/19.55          | ~ (v1_relat_1 @ X5))),
% 19.36/19.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.36/19.55  thf('288', plain,
% 19.36/19.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))
% 19.36/19.55        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['286', '287'])).
% 19.36/19.55  thf('289', plain,
% 19.36/19.55      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 19.36/19.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.36/19.55  thf('290', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 19.36/19.55      inference('demod', [status(thm)], ['288', '289'])).
% 19.36/19.55  thf('291', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('293', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('294', plain,
% 19.36/19.55      ((![X0 : $i]:
% 19.36/19.55          ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0)
% 19.36/19.55           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('demod', [status(thm)],
% 19.36/19.55                ['273', '274', '275', '276', '290', '291', '292', '293'])).
% 19.36/19.55  thf('295', plain,
% 19.36/19.55      ((![X0 : $i]:
% 19.36/19.55          (~ (v1_relat_1 @ sk_C)
% 19.36/19.55           | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55           | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0)))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('sup-', [status(thm)], ['130', '294'])).
% 19.36/19.55  thf('296', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('297', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('298', plain,
% 19.36/19.55      ((![X0 : $i]: (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0))
% 19.36/19.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 19.36/19.55      inference('demod', [status(thm)], ['295', '296', '297'])).
% 19.36/19.55  thf('299', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 19.36/19.55      inference('demod', [status(thm)], ['129', '298'])).
% 19.36/19.55  thf('300', plain,
% 19.36/19.55      (~
% 19.36/19.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 19.36/19.55       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 19.36/19.55       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('split', [status(esa)], ['0'])).
% 19.36/19.55  thf('301', plain,
% 19.36/19.55      (~
% 19.36/19.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 19.36/19.55      inference('sat_resolution*', [status(thm)], ['106', '299', '300'])).
% 19.36/19.55  thf('302', plain,
% 19.36/19.55      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 19.36/19.55      inference('simpl_trail', [status(thm)], ['99', '301'])).
% 19.36/19.55  thf('303', plain,
% 19.36/19.55      (![X10 : $i]:
% 19.36/19.55         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 19.36/19.55          | ~ (v1_funct_1 @ X10)
% 19.36/19.55          | ~ (v1_relat_1 @ X10))),
% 19.36/19.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 19.36/19.55  thf('304', plain,
% 19.36/19.55      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 19.36/19.55      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 19.36/19.55  thf('305', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['96', '97'])).
% 19.36/19.55  thf('306', plain,
% 19.36/19.55      (~
% 19.36/19.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 19.36/19.55      inference('sat_resolution*', [status(thm)], ['106', '299', '300'])).
% 19.36/19.55  thf('307', plain, (((sk_B) = (k1_xboole_0))),
% 19.36/19.55      inference('simpl_trail', [status(thm)], ['305', '306'])).
% 19.36/19.55  thf('308', plain,
% 19.36/19.55      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['304', '307'])).
% 19.36/19.55  thf('309', plain,
% 19.36/19.55      (![X25 : $i, X26 : $i]:
% 19.36/19.55         (~ (m1_subset_1 @ X26 @ 
% 19.36/19.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 19.36/19.55          | ~ (v1_funct_2 @ X26 @ X25 @ k1_xboole_0)
% 19.36/19.55          | ((X26) = (k1_xboole_0))
% 19.36/19.55          | ((X25) = (k1_xboole_0)))),
% 19.36/19.55      inference('simplify', [status(thm)], ['215'])).
% 19.36/19.55  thf('310', plain,
% 19.36/19.55      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 19.36/19.55        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55             (k1_relat_1 @ sk_C) @ k1_xboole_0))),
% 19.36/19.55      inference('sup-', [status(thm)], ['308', '309'])).
% 19.36/19.55  thf('311', plain,
% 19.36/19.55      ((((sk_B) = (k1_xboole_0)))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['96', '97'])).
% 19.36/19.55  thf('312', plain,
% 19.36/19.55      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_relat_1 @ sk_C) @ sk_B)),
% 19.36/19.55      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 19.36/19.55  thf('313', plain,
% 19.36/19.55      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55         (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 19.36/19.55         <= (~
% 19.36/19.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 19.36/19.55      inference('sup+', [status(thm)], ['311', '312'])).
% 19.36/19.55  thf('314', plain,
% 19.36/19.55      (~
% 19.36/19.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 19.36/19.55      inference('sat_resolution*', [status(thm)], ['106', '299', '300'])).
% 19.36/19.55  thf('315', plain,
% 19.36/19.55      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 19.36/19.55        (k1_relat_1 @ sk_C) @ k1_xboole_0)),
% 19.36/19.55      inference('simpl_trail', [status(thm)], ['313', '314'])).
% 19.36/19.55  thf('316', plain,
% 19.36/19.55      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['310', '315'])).
% 19.36/19.55  thf('317', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (((k1_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ X0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['161'])).
% 19.36/19.55  thf('318', plain,
% 19.36/19.55      ((((k1_relat_1 @ sk_C) = (k1_relat_1 @ k1_xboole_0))
% 19.36/19.55        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55        | ~ (v1_relat_1 @ sk_C)
% 19.36/19.55        | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55        | ~ (v2_funct_1 @ sk_C))),
% 19.36/19.55      inference('sup+', [status(thm)], ['316', '317'])).
% 19.36/19.55  thf('319', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.36/19.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 19.36/19.55  thf('320', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('322', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('323', plain,
% 19.36/19.55      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 19.36/19.55        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['318', '319', '320', '321', '322'])).
% 19.36/19.55  thf('324', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 19.36/19.55      inference('simplify', [status(thm)], ['323'])).
% 19.36/19.55  thf('325', plain,
% 19.36/19.55      (![X12 : $i]:
% 19.36/19.55         (~ (v2_funct_1 @ X12)
% 19.36/19.55          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 19.36/19.55          | ~ (v1_funct_1 @ X12)
% 19.36/19.55          | ~ (v1_relat_1 @ X12))),
% 19.36/19.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 19.36/19.55  thf('326', plain,
% 19.36/19.55      (![X28 : $i, X29 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 19.36/19.55          | (m1_subset_1 @ X28 @ 
% 19.36/19.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ X29)))
% 19.36/19.55          | ~ (v1_funct_1 @ X28)
% 19.36/19.55          | ~ (v1_relat_1 @ X28))),
% 19.36/19.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 19.36/19.55  thf('327', plain,
% 19.36/19.55      (![X0 : $i, X1 : $i]:
% 19.36/19.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 19.36/19.55          | ~ (v1_relat_1 @ X0)
% 19.36/19.55          | ~ (v1_funct_1 @ X0)
% 19.36/19.55          | ~ (v2_funct_1 @ X0)
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['325', '326'])).
% 19.36/19.55  thf('328', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55             (k1_zfmisc_1 @ 
% 19.36/19.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 19.36/19.55          | ~ (v2_funct_1 @ sk_C)
% 19.36/19.55          | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55          | ~ (v1_relat_1 @ sk_C))),
% 19.36/19.55      inference('sup-', [status(thm)], ['324', '327'])).
% 19.36/19.55  thf('329', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 19.36/19.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.36/19.55  thf('330', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)],
% 19.36/19.55                ['236', '237', '238', '239', '240', '241'])).
% 19.36/19.55  thf('331', plain, (((sk_B) = (k1_xboole_0))),
% 19.36/19.55      inference('simpl_trail', [status(thm)], ['305', '306'])).
% 19.36/19.55  thf('332', plain, (((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)], ['330', '331'])).
% 19.36/19.55  thf('333', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 19.36/19.55      inference('demod', [status(thm)], ['288', '289'])).
% 19.36/19.55  thf('334', plain, ((v2_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('335', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('336', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('337', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 19.36/19.55          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 19.36/19.55      inference('demod', [status(thm)],
% 19.36/19.55                ['328', '329', '332', '333', '334', '335', '336'])).
% 19.36/19.55  thf('338', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (~ (v1_relat_1 @ sk_C)
% 19.36/19.55          | ~ (v1_funct_1 @ sk_C)
% 19.36/19.55          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))))),
% 19.36/19.55      inference('sup-', [status(thm)], ['303', '337'])).
% 19.36/19.55  thf('339', plain, ((v1_relat_1 @ sk_C)),
% 19.36/19.55      inference('demod', [status(thm)], ['61', '62'])).
% 19.36/19.55  thf('340', plain, ((v1_funct_1 @ sk_C)),
% 19.36/19.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.55  thf('341', plain,
% 19.36/19.55      (![X0 : $i]:
% 19.36/19.55         (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 19.36/19.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 19.36/19.55      inference('demod', [status(thm)], ['338', '339', '340'])).
% 19.36/19.55  thf('342', plain, ($false), inference('demod', [status(thm)], ['302', '341'])).
% 19.36/19.55  
% 19.36/19.55  % SZS output end Refutation
% 19.36/19.55  
% 19.36/19.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
