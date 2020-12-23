%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uQ7visz5eK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:49 EST 2020

% Result     : Theorem 12.92s
% Output     : Refutation 12.92s
% Verified   : 
% Statistics : Number of formulae       :  289 (11135 expanded)
%              Number of leaves         :   42 (3282 expanded)
%              Depth                    :   35
%              Number of atoms          : 2614 (176783 expanded)
%              Number of equality atoms :  116 (6936 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35','40','41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('56',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('61',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','77'])).

thf('79',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('82',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('84',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ( sk_B
        = ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('89',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( sk_B
        = ( k9_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ( sk_B
          = ( k9_relat_1 @ sk_C @ X0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('94',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('102',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('109',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('113',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','109','110','111','112'])).

thf('114',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('115',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','109','110','111','112'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('125',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('127',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('133',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','109','110','111','112'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('137',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_B )
      | ( sk_B
        = ( k1_relset_1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('146',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('147',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('148',plain,
    ( ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('151',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['149','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['152'])).

thf('154',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['148','153'])).

thf('155',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('156',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('157',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','109','110','111','112'])).

thf('158',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','154','155','156','157'])).

thf('159',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['133','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('170',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['122','159','170'])).

thf('172',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['78','175'])).

thf('177',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('178',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['53','176','177'])).

thf('179',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['46','178'])).

thf('180',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( sk_B
        = ( k9_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90','91'])).

thf('183',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ( sk_B
          = ( k9_relat_1 @ sk_C @ X0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('185',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('186',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('188',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('192',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('195',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('199',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('201',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('202',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['200','203'])).

thf('205',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('206',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('210',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208','209'])).

thf('211',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('213',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('215',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218'])).

thf('220',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('221',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('223',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('224',plain,
    ( ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_B )
      | ( sk_B
        = ( k1_relset_1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('226',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218'])).

thf('227',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('228',plain,
    ( ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['152'])).

thf('230',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('232',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('233',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('234',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['224','225','230','231','232','233'])).

thf('235',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['221','234'])).

thf('236',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['53','176','177'])).

thf('237',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['235','236'])).

thf('238',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['210','237'])).

thf('239',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['53','176','177'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['180','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    $false ),
    inference(demod,[status(thm)],['179','244'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uQ7visz5eK
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 12.92/13.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.92/13.12  % Solved by: fo/fo7.sh
% 12.92/13.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.92/13.12  % done 5476 iterations in 12.671s
% 12.92/13.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.92/13.12  % SZS output start Refutation
% 12.92/13.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.92/13.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 12.92/13.12  thf(sk_A_type, type, sk_A: $i).
% 12.92/13.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.92/13.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.92/13.12  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 12.92/13.12  thf(sk_C_type, type, sk_C: $i).
% 12.92/13.12  thf(sk_B_type, type, sk_B: $i).
% 12.92/13.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.92/13.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.92/13.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.92/13.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.92/13.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.92/13.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.92/13.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.92/13.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.92/13.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.92/13.12  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 12.92/13.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.92/13.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.92/13.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.92/13.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.92/13.12  thf(t31_funct_2, conjecture,
% 12.92/13.12    (![A:$i,B:$i,C:$i]:
% 12.92/13.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.92/13.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.92/13.12       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.92/13.12         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.92/13.12           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.92/13.12           ( m1_subset_1 @
% 12.92/13.12             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 12.92/13.12  thf(zf_stmt_0, negated_conjecture,
% 12.92/13.12    (~( ![A:$i,B:$i,C:$i]:
% 12.92/13.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.92/13.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.92/13.12          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.92/13.12            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.92/13.12              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.92/13.12              ( m1_subset_1 @
% 12.92/13.12                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 12.92/13.12    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 12.92/13.12  thf('0', plain,
% 12.92/13.12      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.12        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.92/13.12        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.12  thf('1', plain,
% 12.92/13.12      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.92/13.12         <= (~
% 12.92/13.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.12      inference('split', [status(esa)], ['0'])).
% 12.92/13.12  thf(d1_funct_2, axiom,
% 12.92/13.12    (![A:$i,B:$i,C:$i]:
% 12.92/13.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.92/13.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.92/13.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.92/13.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.92/13.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.92/13.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.92/13.12  thf(zf_stmt_1, axiom,
% 12.92/13.12    (![B:$i,A:$i]:
% 12.92/13.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.92/13.12       ( zip_tseitin_0 @ B @ A ) ))).
% 12.92/13.12  thf('2', plain,
% 12.92/13.12      (![X29 : $i, X30 : $i]:
% 12.92/13.12         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.92/13.12  thf('3', plain,
% 12.92/13.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.12  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.92/13.12  thf(zf_stmt_3, axiom,
% 12.92/13.12    (![C:$i,B:$i,A:$i]:
% 12.92/13.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.92/13.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.92/13.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 12.92/13.12  thf(zf_stmt_5, axiom,
% 12.92/13.12    (![A:$i,B:$i,C:$i]:
% 12.92/13.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.92/13.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.92/13.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.92/13.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.92/13.12  thf('4', plain,
% 12.92/13.12      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.92/13.12         (~ (zip_tseitin_0 @ X34 @ X35)
% 12.92/13.12          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 12.92/13.12          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.92/13.12  thf('5', plain,
% 12.92/13.12      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.92/13.12      inference('sup-', [status(thm)], ['3', '4'])).
% 12.92/13.12  thf('6', plain,
% 12.92/13.12      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.92/13.12      inference('sup-', [status(thm)], ['2', '5'])).
% 12.92/13.12  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.12  thf('8', plain,
% 12.92/13.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.92/13.12         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 12.92/13.12          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 12.92/13.12          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.92/13.12  thf('9', plain,
% 12.92/13.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 12.92/13.12        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 12.92/13.12      inference('sup-', [status(thm)], ['7', '8'])).
% 12.92/13.12  thf('10', plain,
% 12.92/13.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.12  thf(redefinition_k1_relset_1, axiom,
% 12.92/13.12    (![A:$i,B:$i,C:$i]:
% 12.92/13.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.92/13.12  thf('11', plain,
% 12.92/13.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 12.92/13.12         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 12.92/13.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 12.92/13.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.92/13.13  thf('12', plain,
% 12.92/13.13      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 12.92/13.13      inference('sup-', [status(thm)], ['10', '11'])).
% 12.92/13.13  thf('13', plain,
% 12.92/13.13      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.92/13.13      inference('demod', [status(thm)], ['9', '12'])).
% 12.92/13.13  thf('14', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['6', '13'])).
% 12.92/13.13  thf(t55_funct_1, axiom,
% 12.92/13.13    (![A:$i]:
% 12.92/13.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.92/13.13       ( ( v2_funct_1 @ A ) =>
% 12.92/13.13         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 12.92/13.13           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 12.92/13.13  thf('15', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf(dt_k2_funct_1, axiom,
% 12.92/13.13    (![A:$i]:
% 12.92/13.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.92/13.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 12.92/13.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 12.92/13.13  thf('16', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('17', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('18', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf(d10_xboole_0, axiom,
% 12.92/13.13    (![A:$i,B:$i]:
% 12.92/13.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.92/13.13  thf('19', plain,
% 12.92/13.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 12.92/13.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.92/13.13  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.92/13.13      inference('simplify', [status(thm)], ['19'])).
% 12.92/13.13  thf(t4_funct_2, axiom,
% 12.92/13.13    (![A:$i,B:$i]:
% 12.92/13.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 12.92/13.13       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 12.92/13.13         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 12.92/13.13           ( m1_subset_1 @
% 12.92/13.13             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 12.92/13.13  thf('21', plain,
% 12.92/13.13      (![X37 : $i, X38 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 12.92/13.13          | (m1_subset_1 @ X37 @ 
% 12.92/13.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 12.92/13.13          | ~ (v1_funct_1 @ X37)
% 12.92/13.13          | ~ (v1_relat_1 @ X37))),
% 12.92/13.13      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.92/13.13  thf('22', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ X0 @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['20', '21'])).
% 12.92/13.13  thf('23', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13           (k1_zfmisc_1 @ 
% 12.92/13.13            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['18', '22'])).
% 12.92/13.13  thf('24', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 12.92/13.13               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['17', '23'])).
% 12.92/13.13  thf('25', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13           (k1_zfmisc_1 @ 
% 12.92/13.13            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0))),
% 12.92/13.13      inference('simplify', [status(thm)], ['24'])).
% 12.92/13.13  thf('26', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 12.92/13.13               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['16', '25'])).
% 12.92/13.13  thf('27', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13           (k1_zfmisc_1 @ 
% 12.92/13.13            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0))),
% 12.92/13.13      inference('simplify', [status(thm)], ['26'])).
% 12.92/13.13  thf('28', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup+', [status(thm)], ['15', '27'])).
% 12.92/13.13  thf('29', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 12.92/13.13      inference('simplify', [status(thm)], ['28'])).
% 12.92/13.13  thf('30', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 12.92/13.13        | ((sk_B) = (k1_xboole_0))
% 12.92/13.13        | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13        | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13        | ~ (v2_funct_1 @ sk_C))),
% 12.92/13.13      inference('sup+', [status(thm)], ['14', '29'])).
% 12.92/13.13  thf('31', plain,
% 12.92/13.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf(redefinition_k2_relset_1, axiom,
% 12.92/13.13    (![A:$i,B:$i,C:$i]:
% 12.92/13.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 12.92/13.13  thf('32', plain,
% 12.92/13.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 12.92/13.13         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 12.92/13.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 12.92/13.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 12.92/13.13  thf('33', plain,
% 12.92/13.13      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 12.92/13.13      inference('sup-', [status(thm)], ['31', '32'])).
% 12.92/13.13  thf('34', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('35', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('36', plain,
% 12.92/13.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf(cc2_relat_1, axiom,
% 12.92/13.13    (![A:$i]:
% 12.92/13.13     ( ( v1_relat_1 @ A ) =>
% 12.92/13.13       ( ![B:$i]:
% 12.92/13.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 12.92/13.13  thf('37', plain,
% 12.92/13.13      (![X7 : $i, X8 : $i]:
% 12.92/13.13         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 12.92/13.13          | (v1_relat_1 @ X7)
% 12.92/13.13          | ~ (v1_relat_1 @ X8))),
% 12.92/13.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.92/13.13  thf('38', plain,
% 12.92/13.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 12.92/13.13      inference('sup-', [status(thm)], ['36', '37'])).
% 12.92/13.13  thf(fc6_relat_1, axiom,
% 12.92/13.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 12.92/13.13  thf('39', plain,
% 12.92/13.13      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 12.92/13.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.92/13.13  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('43', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 12.92/13.13        | ((sk_B) = (k1_xboole_0)))),
% 12.92/13.13      inference('demod', [status(thm)], ['30', '35', '40', '41', '42'])).
% 12.92/13.13  thf('44', plain,
% 12.92/13.13      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('split', [status(esa)], ['0'])).
% 12.92/13.13  thf('45', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('46', plain,
% 12.92/13.13      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['1', '45'])).
% 12.92/13.13  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('48', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('49', plain,
% 12.92/13.13      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.92/13.13      inference('split', [status(esa)], ['0'])).
% 12.92/13.13  thf('50', plain,
% 12.92/13.13      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['48', '49'])).
% 12.92/13.13  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('52', plain,
% 12.92/13.13      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.92/13.13      inference('demod', [status(thm)], ['50', '51'])).
% 12.92/13.13  thf('53', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['47', '52'])).
% 12.92/13.13  thf('54', plain,
% 12.92/13.13      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('split', [status(esa)], ['0'])).
% 12.92/13.13  thf('55', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['6', '13'])).
% 12.92/13.13  thf('56', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf('57', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('58', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('59', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.92/13.13      inference('simplify', [status(thm)], ['19'])).
% 12.92/13.13  thf('61', plain,
% 12.92/13.13      (![X37 : $i, X38 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 12.92/13.13          | (v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ X38)
% 12.92/13.13          | ~ (v1_funct_1 @ X37)
% 12.92/13.13          | ~ (v1_relat_1 @ X37))),
% 12.92/13.13      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.92/13.13  thf('62', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['60', '61'])).
% 12.92/13.13  thf('63', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['59', '62'])).
% 12.92/13.13  thf('64', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['58', '63'])).
% 12.92/13.13  thf('65', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0))),
% 12.92/13.13      inference('simplify', [status(thm)], ['64'])).
% 12.92/13.13  thf('66', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['57', '65'])).
% 12.92/13.13  thf('67', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0))),
% 12.92/13.13      inference('simplify', [status(thm)], ['66'])).
% 12.92/13.13  thf('68', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13           (k1_relat_1 @ X0))
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup+', [status(thm)], ['56', '67'])).
% 12.92/13.13  thf('69', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13             (k1_relat_1 @ X0)))),
% 12.92/13.13      inference('simplify', [status(thm)], ['68'])).
% 12.92/13.13  thf('70', plain,
% 12.92/13.13      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 12.92/13.13        | ((sk_B) = (k1_xboole_0))
% 12.92/13.13        | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13        | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13        | ~ (v2_funct_1 @ sk_C))),
% 12.92/13.13      inference('sup+', [status(thm)], ['55', '69'])).
% 12.92/13.13  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('75', plain,
% 12.92/13.13      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.92/13.13        | ((sk_B) = (k1_xboole_0)))),
% 12.92/13.13      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 12.92/13.13  thf('76', plain,
% 12.92/13.13      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('split', [status(esa)], ['0'])).
% 12.92/13.13  thf('77', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('78', plain,
% 12.92/13.13      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['54', '77'])).
% 12.92/13.13  thf('79', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('80', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('81', plain,
% 12.92/13.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf(dt_k7_relset_1, axiom,
% 12.92/13.13    (![A:$i,B:$i,C:$i,D:$i]:
% 12.92/13.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.13       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 12.92/13.13  thf('82', plain,
% 12.92/13.13      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 12.92/13.13         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 12.92/13.13          | (m1_subset_1 @ (k7_relset_1 @ X16 @ X17 @ X15 @ X18) @ 
% 12.92/13.13             (k1_zfmisc_1 @ X17)))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 12.92/13.13  thf('83', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 12.92/13.13          (k1_zfmisc_1 @ sk_B))),
% 12.92/13.13      inference('sup-', [status(thm)], ['81', '82'])).
% 12.92/13.13  thf(t3_subset, axiom,
% 12.92/13.13    (![A:$i,B:$i]:
% 12.92/13.13     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.92/13.13  thf('84', plain,
% 12.92/13.13      (![X4 : $i, X5 : $i]:
% 12.92/13.13         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 12.92/13.13      inference('cnf', [status(esa)], [t3_subset])).
% 12.92/13.13  thf('85', plain,
% 12.92/13.13      (![X0 : $i]: (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) @ sk_B)),
% 12.92/13.13      inference('sup-', [status(thm)], ['83', '84'])).
% 12.92/13.13  thf('86', plain,
% 12.92/13.13      (![X0 : $i, X2 : $i]:
% 12.92/13.13         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.92/13.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.92/13.13  thf('87', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (r1_tarski @ sk_B @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0))
% 12.92/13.13          | ((sk_B) = (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['85', '86'])).
% 12.92/13.13  thf('88', plain,
% 12.92/13.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf(redefinition_k7_relset_1, axiom,
% 12.92/13.13    (![A:$i,B:$i,C:$i,D:$i]:
% 12.92/13.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.92/13.13       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 12.92/13.13  thf('89', plain,
% 12.92/13.13      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 12.92/13.13         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 12.92/13.13          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 12.92/13.13      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 12.92/13.13  thf('90', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['88', '89'])).
% 12.92/13.13  thf('91', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['88', '89'])).
% 12.92/13.13  thf('92', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (r1_tarski @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 12.92/13.13          | ((sk_B) = (k9_relat_1 @ sk_C @ X0)))),
% 12.92/13.13      inference('demod', [status(thm)], ['87', '90', '91'])).
% 12.92/13.13  thf('93', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 12.92/13.13           | ((sk_B) = (k9_relat_1 @ sk_C @ X0))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['80', '92'])).
% 12.92/13.13  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 12.92/13.13  thf('94', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.92/13.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.92/13.13  thf('95', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('96', plain,
% 12.92/13.13      ((![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_C @ X0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['93', '94', '95'])).
% 12.92/13.13  thf('97', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.92/13.13      inference('simplify', [status(thm)], ['19'])).
% 12.92/13.13  thf(t164_funct_1, axiom,
% 12.92/13.13    (![A:$i,B:$i]:
% 12.92/13.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 12.92/13.13       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 12.92/13.13         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 12.92/13.13  thf('98', plain,
% 12.92/13.13      (![X12 : $i, X13 : $i]:
% 12.92/13.13         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 12.92/13.13          | ~ (v2_funct_1 @ X13)
% 12.92/13.13          | ((k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)) = (X12))
% 12.92/13.13          | ~ (v1_funct_1 @ X13)
% 12.92/13.13          | ~ (v1_relat_1 @ X13))),
% 12.92/13.13      inference('cnf', [status(esa)], [t164_funct_1])).
% 12.92/13.13  thf('99', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 12.92/13.13              = (k1_relat_1 @ X0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['97', '98'])).
% 12.92/13.13  thf('100', plain,
% 12.92/13.13      (((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_relat_1 @ sk_C))
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['96', '99'])).
% 12.92/13.13  thf('101', plain,
% 12.92/13.13      ((![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_C @ X0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['93', '94', '95'])).
% 12.92/13.13  thf('102', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.92/13.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.92/13.13  thf('103', plain,
% 12.92/13.13      (![X12 : $i, X13 : $i]:
% 12.92/13.13         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 12.92/13.13          | ~ (v2_funct_1 @ X13)
% 12.92/13.13          | ((k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)) = (X12))
% 12.92/13.13          | ~ (v1_funct_1 @ X13)
% 12.92/13.13          | ~ (v1_relat_1 @ X13))),
% 12.92/13.13      inference('cnf', [status(esa)], [t164_funct_1])).
% 12.92/13.13  thf('104', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 12.92/13.13              = (k1_xboole_0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['102', '103'])).
% 12.92/13.13  thf('105', plain,
% 12.92/13.13      (((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['101', '104'])).
% 12.92/13.13  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('109', plain,
% 12.92/13.13      ((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 12.92/13.13  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('113', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['100', '109', '110', '111', '112'])).
% 12.92/13.13  thf('114', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf('115', plain,
% 12.92/13.13      (![X37 : $i, X38 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 12.92/13.13          | (v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ X38)
% 12.92/13.13          | ~ (v1_funct_1 @ X37)
% 12.92/13.13          | ~ (v1_relat_1 @ X37))),
% 12.92/13.13      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.92/13.13  thf('116', plain,
% 12.92/13.13      (![X0 : $i, X1 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 12.92/13.13      inference('sup-', [status(thm)], ['114', '115'])).
% 12.92/13.13  thf('117', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 12.92/13.13           | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13              (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.13           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.13           | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13           | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13           | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['113', '116'])).
% 12.92/13.13  thf('118', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.92/13.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.92/13.13  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('122', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13            (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.13           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 12.92/13.13  thf('123', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['100', '109', '110', '111', '112'])).
% 12.92/13.13  thf('124', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 12.92/13.13      inference('simplify', [status(thm)], ['28'])).
% 12.92/13.13  thf('125', plain,
% 12.92/13.13      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ k1_xboole_0)))
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['123', '124'])).
% 12.92/13.13  thf('126', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('127', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('131', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['125', '126', '127', '128', '129', '130'])).
% 12.92/13.13  thf('132', plain,
% 12.92/13.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 12.92/13.13         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 12.92/13.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 12.92/13.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.92/13.13  thf('133', plain,
% 12.92/13.13      ((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 12.92/13.13          = (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['131', '132'])).
% 12.92/13.13  thf('134', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['100', '109', '110', '111', '112'])).
% 12.92/13.13  thf('135', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('136', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 12.92/13.13             (k1_relat_1 @ X0)))),
% 12.92/13.13      inference('simplify', [status(thm)], ['68'])).
% 12.92/13.13  thf('137', plain,
% 12.92/13.13      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 12.92/13.13        | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13        | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13        | ~ (v2_funct_1 @ sk_C))),
% 12.92/13.13      inference('sup+', [status(thm)], ['135', '136'])).
% 12.92/13.13  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('141', plain,
% 12.92/13.13      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 12.92/13.13      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 12.92/13.13  thf('142', plain,
% 12.92/13.13      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.92/13.13         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 12.92/13.13          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 12.92/13.13          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.92/13.13  thf('143', plain,
% 12.92/13.13      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ sk_B)
% 12.92/13.13        | ((sk_B)
% 12.92/13.13            = (k1_relset_1 @ sk_B @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['141', '142'])).
% 12.92/13.13  thf('144', plain,
% 12.92/13.13      (((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_B)
% 12.92/13.13         | ((sk_B)
% 12.92/13.13             = (k1_relset_1 @ sk_B @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C)))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['134', '143'])).
% 12.92/13.13  thf('145', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('146', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['125', '126', '127', '128', '129', '130'])).
% 12.92/13.13  thf('147', plain,
% 12.92/13.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.92/13.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 12.92/13.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 12.92/13.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.92/13.13  thf('148', plain,
% 12.92/13.13      ((((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 12.92/13.13         | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['146', '147'])).
% 12.92/13.13  thf('149', plain,
% 12.92/13.13      (![X29 : $i, X30 : $i]:
% 12.92/13.13         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.92/13.13  thf('150', plain,
% 12.92/13.13      (![X29 : $i, X30 : $i]:
% 12.92/13.13         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.92/13.13  thf('151', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 12.92/13.13      inference('simplify', [status(thm)], ['150'])).
% 12.92/13.13  thf('152', plain,
% 12.92/13.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.92/13.13         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 12.92/13.13      inference('sup+', [status(thm)], ['149', '151'])).
% 12.92/13.13  thf('153', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 12.92/13.13      inference('eq_fact', [status(thm)], ['152'])).
% 12.92/13.13  thf('154', plain,
% 12.92/13.13      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['148', '153'])).
% 12.92/13.13  thf('155', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('156', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['75', '76'])).
% 12.92/13.13  thf('157', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['100', '109', '110', '111', '112'])).
% 12.92/13.13  thf('158', plain,
% 12.92/13.13      ((((k1_xboole_0)
% 12.92/13.13          = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['144', '145', '154', '155', '156', '157'])).
% 12.92/13.13  thf('159', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup+', [status(thm)], ['133', '158'])).
% 12.92/13.13  thf('160', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('161', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 12.92/13.13      inference('simplify', [status(thm)], ['28'])).
% 12.92/13.13  thf('162', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 12.92/13.13        | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13        | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13        | ~ (v2_funct_1 @ sk_C))),
% 12.92/13.13      inference('sup+', [status(thm)], ['160', '161'])).
% 12.92/13.13  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('166', plain,
% 12.92/13.13      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 12.92/13.13      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 12.92/13.13  thf('167', plain,
% 12.92/13.13      (![X7 : $i, X8 : $i]:
% 12.92/13.13         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 12.92/13.13          | (v1_relat_1 @ X7)
% 12.92/13.13          | ~ (v1_relat_1 @ X8))),
% 12.92/13.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.92/13.13  thf('168', plain,
% 12.92/13.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))
% 12.92/13.13        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['166', '167'])).
% 12.92/13.13  thf('169', plain,
% 12.92/13.13      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 12.92/13.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.92/13.13  thf('170', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 12.92/13.13      inference('demod', [status(thm)], ['168', '169'])).
% 12.92/13.13  thf('171', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0)
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['122', '159', '170'])).
% 12.92/13.13  thf('172', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          (~ (v1_relat_1 @ sk_C)
% 12.92/13.13           | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13           | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0)))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('sup-', [status(thm)], ['79', '171'])).
% 12.92/13.13  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('175', plain,
% 12.92/13.13      ((![X0 : $i]: (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ X0))
% 12.92/13.13         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.92/13.13      inference('demod', [status(thm)], ['172', '173', '174'])).
% 12.92/13.13  thf('176', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 12.92/13.13      inference('demod', [status(thm)], ['78', '175'])).
% 12.92/13.13  thf('177', plain,
% 12.92/13.13      (~
% 12.92/13.13       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 12.92/13.13       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 12.92/13.13       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.92/13.13      inference('split', [status(esa)], ['0'])).
% 12.92/13.13  thf('178', plain,
% 12.92/13.13      (~
% 12.92/13.13       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.92/13.13      inference('sat_resolution*', [status(thm)], ['53', '176', '177'])).
% 12.92/13.13  thf('179', plain,
% 12.92/13.13      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 12.92/13.13      inference('simpl_trail', [status(thm)], ['46', '178'])).
% 12.92/13.13  thf('180', plain,
% 12.92/13.13      (![X11 : $i]:
% 12.92/13.13         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 12.92/13.13          | ~ (v1_funct_1 @ X11)
% 12.92/13.13          | ~ (v1_relat_1 @ X11))),
% 12.92/13.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.92/13.13  thf('181', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('182', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (r1_tarski @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 12.92/13.13          | ((sk_B) = (k9_relat_1 @ sk_C @ X0)))),
% 12.92/13.13      inference('demod', [status(thm)], ['87', '90', '91'])).
% 12.92/13.13  thf('183', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 12.92/13.13           | ((sk_B) = (k9_relat_1 @ sk_C @ X0))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['181', '182'])).
% 12.92/13.13  thf('184', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.92/13.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.92/13.13  thf('185', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('186', plain,
% 12.92/13.13      ((![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_C @ X0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['183', '184', '185'])).
% 12.92/13.13  thf('187', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 12.92/13.13              = (k1_relat_1 @ X0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['97', '98'])).
% 12.92/13.13  thf('188', plain,
% 12.92/13.13      (((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_relat_1 @ sk_C))
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['186', '187'])).
% 12.92/13.13  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('192', plain,
% 12.92/13.13      ((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 12.92/13.13  thf('193', plain,
% 12.92/13.13      ((![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_C @ X0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['183', '184', '185'])).
% 12.92/13.13  thf('194', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 12.92/13.13              = (k1_xboole_0))
% 12.92/13.13          | ~ (v2_funct_1 @ X0))),
% 12.92/13.13      inference('sup-', [status(thm)], ['102', '103'])).
% 12.92/13.13  thf('195', plain,
% 12.92/13.13      (((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['193', '194'])).
% 12.92/13.13  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('199', plain,
% 12.92/13.13      ((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 12.92/13.13  thf('200', plain,
% 12.92/13.13      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['192', '199'])).
% 12.92/13.13  thf('201', plain,
% 12.92/13.13      (![X14 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X14)
% 12.92/13.13          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 12.92/13.13          | ~ (v1_funct_1 @ X14)
% 12.92/13.13          | ~ (v1_relat_1 @ X14))),
% 12.92/13.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.92/13.13  thf('202', plain,
% 12.92/13.13      (![X37 : $i, X38 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 12.92/13.13          | (m1_subset_1 @ X37 @ 
% 12.92/13.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 12.92/13.13          | ~ (v1_funct_1 @ X37)
% 12.92/13.13          | ~ (v1_relat_1 @ X37))),
% 12.92/13.13      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.92/13.13  thf('203', plain,
% 12.92/13.13      (![X0 : $i, X1 : $i]:
% 12.92/13.13         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['201', '202'])).
% 12.92/13.13  thf('204', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 12.92/13.13           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13              (k1_zfmisc_1 @ 
% 12.92/13.13               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.13           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.92/13.13           | ~ (v2_funct_1 @ sk_C)
% 12.92/13.13           | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13           | ~ (v1_relat_1 @ sk_C)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['200', '203'])).
% 12.92/13.13  thf('205', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 12.92/13.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.92/13.13  thf('206', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 12.92/13.13      inference('demod', [status(thm)], ['168', '169'])).
% 12.92/13.13  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('210', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13            (k1_zfmisc_1 @ 
% 12.92/13.13             (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['204', '205', '206', '207', '208', '209'])).
% 12.92/13.13  thf('211', plain,
% 12.92/13.13      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['192', '199'])).
% 12.92/13.13  thf('212', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v2_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_funct_1 @ X0)
% 12.92/13.13          | ~ (v1_relat_1 @ X0)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 12.92/13.13             (k1_zfmisc_1 @ 
% 12.92/13.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 12.92/13.13      inference('simplify', [status(thm)], ['28'])).
% 12.92/13.13  thf('213', plain,
% 12.92/13.13      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ k1_xboole_0)))
% 12.92/13.13         | ~ (v1_relat_1 @ sk_C)
% 12.92/13.13         | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13         | ~ (v2_funct_1 @ sk_C)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['211', '212'])).
% 12.92/13.13  thf('214', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.92/13.13      inference('sup+', [status(thm)], ['33', '34'])).
% 12.92/13.13  thf('215', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('219', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['213', '214', '215', '216', '217', '218'])).
% 12.92/13.13  thf('220', plain,
% 12.92/13.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 12.92/13.13         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 12.92/13.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 12.92/13.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.92/13.13  thf('221', plain,
% 12.92/13.13      ((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 12.92/13.13          = (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['219', '220'])).
% 12.92/13.13  thf('222', plain,
% 12.92/13.13      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['192', '199'])).
% 12.92/13.13  thf('223', plain,
% 12.92/13.13      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ sk_B)
% 12.92/13.13        | ((sk_B)
% 12.92/13.13            = (k1_relset_1 @ sk_B @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['141', '142'])).
% 12.92/13.13  thf('224', plain,
% 12.92/13.13      (((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_B)
% 12.92/13.13         | ((sk_B)
% 12.92/13.13             = (k1_relset_1 @ sk_B @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C)))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['222', '223'])).
% 12.92/13.13  thf('225', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('226', plain,
% 12.92/13.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['213', '214', '215', '216', '217', '218'])).
% 12.92/13.13  thf('227', plain,
% 12.92/13.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.92/13.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 12.92/13.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 12.92/13.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.92/13.13  thf('228', plain,
% 12.92/13.13      ((((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 12.92/13.13         | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['226', '227'])).
% 12.92/13.13  thf('229', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 12.92/13.13      inference('eq_fact', [status(thm)], ['152'])).
% 12.92/13.13  thf('230', plain,
% 12.92/13.13      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['228', '229'])).
% 12.92/13.13  thf('231', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('232', plain,
% 12.92/13.13      ((((sk_B) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['43', '44'])).
% 12.92/13.13  thf('233', plain,
% 12.92/13.13      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['192', '199'])).
% 12.92/13.13  thf('234', plain,
% 12.92/13.13      ((((k1_xboole_0)
% 12.92/13.13          = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)],
% 12.92/13.13                ['224', '225', '230', '231', '232', '233'])).
% 12.92/13.13  thf('235', plain,
% 12.92/13.13      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('sup+', [status(thm)], ['221', '234'])).
% 12.92/13.13  thf('236', plain,
% 12.92/13.13      (~
% 12.92/13.13       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.92/13.13      inference('sat_resolution*', [status(thm)], ['53', '176', '177'])).
% 12.92/13.13  thf('237', plain, (((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 12.92/13.13      inference('simpl_trail', [status(thm)], ['235', '236'])).
% 12.92/13.13  thf('238', plain,
% 12.92/13.13      ((![X0 : $i]:
% 12.92/13.13          ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13            (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 12.92/13.13           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))))
% 12.92/13.13         <= (~
% 12.92/13.13             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.92/13.13      inference('demod', [status(thm)], ['210', '237'])).
% 12.92/13.13  thf('239', plain,
% 12.92/13.13      (~
% 12.92/13.13       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.92/13.13      inference('sat_resolution*', [status(thm)], ['53', '176', '177'])).
% 12.92/13.13  thf('240', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 12.92/13.13          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.92/13.13      inference('simpl_trail', [status(thm)], ['238', '239'])).
% 12.92/13.13  thf('241', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (~ (v1_relat_1 @ sk_C)
% 12.92/13.13          | ~ (v1_funct_1 @ sk_C)
% 12.92/13.13          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))))),
% 12.92/13.13      inference('sup-', [status(thm)], ['180', '240'])).
% 12.92/13.13  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 12.92/13.13      inference('demod', [status(thm)], ['38', '39'])).
% 12.92/13.13  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 12.92/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.92/13.13  thf('244', plain,
% 12.92/13.13      (![X0 : $i]:
% 12.92/13.13         (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.92/13.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 12.92/13.13      inference('demod', [status(thm)], ['241', '242', '243'])).
% 12.92/13.13  thf('245', plain, ($false), inference('demod', [status(thm)], ['179', '244'])).
% 12.92/13.13  
% 12.92/13.13  % SZS output end Refutation
% 12.92/13.13  
% 12.92/13.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
