%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VmE8pQEMuq

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:56 EST 2020

% Result     : Theorem 5.17s
% Output     : Refutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 865 expanded)
%              Number of leaves         :   51 ( 279 expanded)
%              Depth                    :   25
%              Number of atoms          : 1850 (17527 expanded)
%              Number of equality atoms :  108 (1055 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('4',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('20',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['32','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('53',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['2','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ sk_B ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['0','63'])).

thf('65',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('77',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('81',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['64','79','80','81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('86',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('94',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','100'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('106',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['103','106'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('108',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('113',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('114',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('118',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['103','106'])).

thf('120',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['111','118','119','120','123'])).

thf('125',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['83','124'])).

thf('126',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['121','122'])).

thf('133',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('136',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('137',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('141',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('146',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['133','148'])).

thf('150',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['126','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('152',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('156',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['103','106'])).

thf('157',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['121','122'])).

thf('159',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('160',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['154','160'])).

thf('162',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['125','161'])).

thf('163',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('166',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['163','166'])).

thf('168',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['162','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VmE8pQEMuq
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.17/5.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.17/5.35  % Solved by: fo/fo7.sh
% 5.17/5.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.17/5.35  % done 3316 iterations in 4.878s
% 5.17/5.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.17/5.35  % SZS output start Refutation
% 5.17/5.35  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.17/5.35  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.17/5.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.17/5.35  thf(sk_E_type, type, sk_E: $i).
% 5.17/5.35  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.17/5.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.17/5.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.17/5.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.17/5.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.17/5.35  thf(sk_D_type, type, sk_D: $i).
% 5.17/5.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.17/5.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.17/5.35  thf(sk_C_type, type, sk_C: $i).
% 5.17/5.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.17/5.35  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.17/5.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.17/5.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.17/5.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.17/5.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.17/5.35  thf(sk_A_type, type, sk_A: $i).
% 5.17/5.35  thf(sk_B_type, type, sk_B: $i).
% 5.17/5.35  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.17/5.35  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.17/5.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.17/5.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.17/5.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.17/5.35  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.17/5.35  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.17/5.35  thf(t154_funct_1, axiom,
% 5.17/5.35    (![A:$i,B:$i]:
% 5.17/5.35     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.17/5.35       ( ( v2_funct_1 @ B ) =>
% 5.17/5.35         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 5.17/5.35  thf('0', plain,
% 5.17/5.35      (![X14 : $i, X15 : $i]:
% 5.17/5.35         (~ (v2_funct_1 @ X14)
% 5.17/5.35          | ((k9_relat_1 @ X14 @ X15)
% 5.17/5.35              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 5.17/5.35          | ~ (v1_funct_1 @ X14)
% 5.17/5.35          | ~ (v1_relat_1 @ X14))),
% 5.17/5.35      inference('cnf', [status(esa)], [t154_funct_1])).
% 5.17/5.35  thf(fc6_funct_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.17/5.35       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.17/5.35         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.17/5.35         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.17/5.35  thf('1', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf('2', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf(t55_funct_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.17/5.35       ( ( v2_funct_1 @ A ) =>
% 5.17/5.35         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.17/5.35           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.17/5.35  thf('3', plain,
% 5.17/5.35      (![X16 : $i]:
% 5.17/5.35         (~ (v2_funct_1 @ X16)
% 5.17/5.35          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 5.17/5.35          | ~ (v1_funct_1 @ X16)
% 5.17/5.35          | ~ (v1_relat_1 @ X16))),
% 5.17/5.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.17/5.35  thf(t28_funct_2, conjecture,
% 5.17/5.35    (![A:$i,B:$i,C:$i,D:$i]:
% 5.17/5.35     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.17/5.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.17/5.35       ( ![E:$i]:
% 5.17/5.35         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.17/5.35             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.17/5.35           ( ( ( ( k2_relset_1 @
% 5.17/5.35                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 5.17/5.35                 ( C ) ) & 
% 5.17/5.35               ( v2_funct_1 @ E ) ) =>
% 5.17/5.35             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 5.17/5.35               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 5.17/5.35  thf(zf_stmt_0, negated_conjecture,
% 5.17/5.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.17/5.35        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.17/5.35            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.17/5.35          ( ![E:$i]:
% 5.17/5.35            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.17/5.35                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.17/5.35              ( ( ( ( k2_relset_1 @
% 5.17/5.35                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 5.17/5.35                    ( C ) ) & 
% 5.17/5.35                  ( v2_funct_1 @ E ) ) =>
% 5.17/5.35                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 5.17/5.35                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 5.17/5.35    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 5.17/5.35  thf('4', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(d1_funct_2, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.17/5.35           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.17/5.35             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.17/5.35         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.17/5.35           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.17/5.35             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.17/5.35  thf(zf_stmt_1, axiom,
% 5.17/5.35    (![C:$i,B:$i,A:$i]:
% 5.17/5.35     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.17/5.35       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.17/5.35  thf('5', plain,
% 5.17/5.35      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.17/5.35         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 5.17/5.35          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 5.17/5.35          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.17/5.35  thf('6', plain,
% 5.17/5.35      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 5.17/5.35        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['4', '5'])).
% 5.17/5.35  thf(zf_stmt_2, axiom,
% 5.17/5.35    (![B:$i,A:$i]:
% 5.17/5.35     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.17/5.35       ( zip_tseitin_0 @ B @ A ) ))).
% 5.17/5.35  thf('7', plain,
% 5.17/5.35      (![X30 : $i, X31 : $i]:
% 5.17/5.35         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.17/5.35  thf('8', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.17/5.35  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.17/5.35  thf(zf_stmt_5, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.17/5.35         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.17/5.35           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.17/5.35             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.17/5.35  thf('9', plain,
% 5.17/5.35      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.17/5.35         (~ (zip_tseitin_0 @ X35 @ X36)
% 5.17/5.35          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 5.17/5.35          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.17/5.35  thf('10', plain,
% 5.17/5.35      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 5.17/5.35      inference('sup-', [status(thm)], ['8', '9'])).
% 5.17/5.35  thf('11', plain,
% 5.17/5.35      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 5.17/5.35      inference('sup-', [status(thm)], ['7', '10'])).
% 5.17/5.35  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('13', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 5.17/5.35      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 5.17/5.35  thf('14', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(redefinition_k1_relset_1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.17/5.35  thf('15', plain,
% 5.17/5.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.17/5.35         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 5.17/5.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 5.17/5.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.17/5.35  thf('16', plain,
% 5.17/5.35      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 5.17/5.35      inference('sup-', [status(thm)], ['14', '15'])).
% 5.17/5.35  thf('17', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.17/5.35      inference('demod', [status(thm)], ['6', '13', '16'])).
% 5.17/5.35  thf('18', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf('19', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf('20', plain,
% 5.17/5.35      (![X16 : $i]:
% 5.17/5.35         (~ (v2_funct_1 @ X16)
% 5.17/5.35          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 5.17/5.35          | ~ (v1_funct_1 @ X16)
% 5.17/5.35          | ~ (v1_relat_1 @ X16))),
% 5.17/5.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.17/5.35  thf(d10_xboole_0, axiom,
% 5.17/5.35    (![A:$i,B:$i]:
% 5.17/5.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.17/5.35  thf('21', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.17/5.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.17/5.35  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.17/5.35      inference('simplify', [status(thm)], ['21'])).
% 5.17/5.35  thf(d19_relat_1, axiom,
% 5.17/5.35    (![A:$i,B:$i]:
% 5.17/5.35     ( ( v1_relat_1 @ B ) =>
% 5.17/5.35       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.17/5.35  thf('23', plain,
% 5.17/5.35      (![X3 : $i, X4 : $i]:
% 5.17/5.35         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.17/5.35          | (v5_relat_1 @ X3 @ X4)
% 5.17/5.35          | ~ (v1_relat_1 @ X3))),
% 5.17/5.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.17/5.35  thf('24', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['22', '23'])).
% 5.17/5.35  thf('25', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.17/5.35      inference('sup+', [status(thm)], ['20', '24'])).
% 5.17/5.35  thf('26', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['19', '25'])).
% 5.17/5.35  thf('27', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('simplify', [status(thm)], ['26'])).
% 5.17/5.35  thf('28', plain,
% 5.17/5.35      (![X3 : $i, X4 : $i]:
% 5.17/5.35         (~ (v5_relat_1 @ X3 @ X4)
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.17/5.35          | ~ (v1_relat_1 @ X3))),
% 5.17/5.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.17/5.35  thf('29', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['27', '28'])).
% 5.17/5.35  thf('30', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('sup-', [status(thm)], ['18', '29'])).
% 5.17/5.35  thf('31', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('simplify', [status(thm)], ['30'])).
% 5.17/5.35  thf('32', plain,
% 5.17/5.35      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_E)) @ sk_B)
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E))),
% 5.17/5.35      inference('sup+', [status(thm)], ['17', '31'])).
% 5.17/5.35  thf('33', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(cc1_relset_1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( v1_relat_1 @ C ) ))).
% 5.17/5.35  thf('34', plain,
% 5.17/5.35      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.17/5.35         ((v1_relat_1 @ X18)
% 5.17/5.35          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.17/5.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.17/5.35  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('37', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_E)) @ sk_B)),
% 5.17/5.35      inference('demod', [status(thm)], ['32', '35', '36', '37'])).
% 5.17/5.35  thf('39', plain,
% 5.17/5.35      (![X0 : $i, X2 : $i]:
% 5.17/5.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.17/5.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.17/5.35  thf('40', plain,
% 5.17/5.35      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 5.17/5.35        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E))))),
% 5.17/5.35      inference('sup-', [status(thm)], ['38', '39'])).
% 5.17/5.35  thf('41', plain,
% 5.17/5.35      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_E))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E)
% 5.17/5.35        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E))))),
% 5.17/5.35      inference('sup-', [status(thm)], ['3', '40'])).
% 5.17/5.35  thf('42', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.17/5.35      inference('demod', [status(thm)], ['6', '13', '16'])).
% 5.17/5.35  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.17/5.35      inference('simplify', [status(thm)], ['21'])).
% 5.17/5.35  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('46', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('47', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 5.17/5.35  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.17/5.35      inference('simplify', [status(thm)], ['21'])).
% 5.17/5.35  thf(t147_funct_1, axiom,
% 5.17/5.35    (![A:$i,B:$i]:
% 5.17/5.35     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.17/5.35       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 5.17/5.35         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 5.17/5.35  thf('49', plain,
% 5.17/5.35      (![X12 : $i, X13 : $i]:
% 5.17/5.35         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 5.17/5.35          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 5.17/5.35          | ~ (v1_funct_1 @ X13)
% 5.17/5.35          | ~ (v1_relat_1 @ X13))),
% 5.17/5.35      inference('cnf', [status(esa)], [t147_funct_1])).
% 5.17/5.35  thf('50', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 5.17/5.35              = (k2_relat_1 @ X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['48', '49'])).
% 5.17/5.35  thf('51', plain,
% 5.17/5.35      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35          (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B))
% 5.17/5.35          = (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 5.17/5.35        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('sup+', [status(thm)], ['47', '50'])).
% 5.17/5.35  thf('52', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 5.17/5.35  thf('53', plain,
% 5.17/5.35      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35          (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B))
% 5.17/5.35        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('demod', [status(thm)], ['51', '52'])).
% 5.17/5.35  thf('54', plain,
% 5.17/5.35      ((~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['2', '53'])).
% 5.17/5.35  thf('55', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('57', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('58', plain,
% 5.17/5.35      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B)))),
% 5.17/5.35      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 5.17/5.35  thf('59', plain,
% 5.17/5.35      ((~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E)
% 5.17/5.35        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['1', '58'])).
% 5.17/5.35  thf('60', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('62', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('63', plain,
% 5.17/5.35      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35         (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 5.17/5.35  thf('64', plain,
% 5.17/5.35      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ sk_B))
% 5.17/5.35          = (sk_B))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E))),
% 5.17/5.35      inference('sup+', [status(thm)], ['0', '63'])).
% 5.17/5.35  thf('65', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 5.17/5.35  thf('66', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf(t61_funct_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.17/5.35       ( ( v2_funct_1 @ A ) =>
% 5.17/5.35         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 5.17/5.35             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 5.17/5.35           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 5.17/5.35             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.17/5.35  thf('67', plain,
% 5.17/5.35      (![X17 : $i]:
% 5.17/5.35         (~ (v2_funct_1 @ X17)
% 5.17/5.35          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 5.17/5.35              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 5.17/5.35          | ~ (v1_funct_1 @ X17)
% 5.17/5.35          | ~ (v1_relat_1 @ X17))),
% 5.17/5.35      inference('cnf', [status(esa)], [t61_funct_1])).
% 5.17/5.35  thf(t160_relat_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( v1_relat_1 @ A ) =>
% 5.17/5.35       ( ![B:$i]:
% 5.17/5.35         ( ( v1_relat_1 @ B ) =>
% 5.17/5.35           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.17/5.35             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.17/5.35  thf('68', plain,
% 5.17/5.35      (![X5 : $i, X6 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X5)
% 5.17/5.35          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 5.17/5.35              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 5.17/5.35          | ~ (v1_relat_1 @ X6))),
% 5.17/5.35      inference('cnf', [status(esa)], [t160_relat_1])).
% 5.17/5.35  thf('69', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 5.17/5.35            = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('sup+', [status(thm)], ['67', '68'])).
% 5.17/5.35  thf(t71_relat_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.17/5.35       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.17/5.35  thf('70', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 5.17/5.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.17/5.35  thf('71', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (((k2_relat_1 @ X0)
% 5.17/5.35            = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('demod', [status(thm)], ['69', '70'])).
% 5.17/5.35  thf('72', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ((k2_relat_1 @ X0)
% 5.17/5.35              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 5.17/5.35      inference('simplify', [status(thm)], ['71'])).
% 5.17/5.35  thf('73', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ((k2_relat_1 @ X0)
% 5.17/5.35              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v2_funct_1 @ X0))),
% 5.17/5.35      inference('sup-', [status(thm)], ['66', '72'])).
% 5.17/5.35  thf('74', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (((k2_relat_1 @ X0)
% 5.17/5.35            = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 5.17/5.35          | ~ (v2_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_relat_1 @ X0))),
% 5.17/5.35      inference('simplify', [status(thm)], ['73'])).
% 5.17/5.35  thf('75', plain,
% 5.17/5.35      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E))),
% 5.17/5.35      inference('sup+', [status(thm)], ['65', '74'])).
% 5.17/5.35  thf('76', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('77', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('78', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('79', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 5.17/5.35  thf('80', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('82', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('83', plain,
% 5.17/5.35      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['64', '79', '80', '81', '82'])).
% 5.17/5.35  thf('84', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('85', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(dt_k1_partfun1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.17/5.35     ( ( ( v1_funct_1 @ E ) & 
% 5.17/5.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.17/5.35         ( v1_funct_1 @ F ) & 
% 5.17/5.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.17/5.35       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.17/5.35         ( m1_subset_1 @
% 5.17/5.35           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.17/5.35           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.17/5.35  thf('86', plain,
% 5.17/5.35      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.17/5.35         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.17/5.35          | ~ (v1_funct_1 @ X38)
% 5.17/5.35          | ~ (v1_funct_1 @ X41)
% 5.17/5.35          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.17/5.35          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 5.17/5.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 5.17/5.35      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.17/5.35  thf('87', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 5.17/5.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.17/5.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.17/5.35          | ~ (v1_funct_1 @ X1)
% 5.17/5.35          | ~ (v1_funct_1 @ sk_D))),
% 5.17/5.35      inference('sup-', [status(thm)], ['85', '86'])).
% 5.17/5.35  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('89', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 5.17/5.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.17/5.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.17/5.35          | ~ (v1_funct_1 @ X1))),
% 5.17/5.35      inference('demod', [status(thm)], ['87', '88'])).
% 5.17/5.35  thf('90', plain,
% 5.17/5.35      ((~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | (m1_subset_1 @ 
% 5.17/5.35           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 5.17/5.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 5.17/5.35      inference('sup-', [status(thm)], ['84', '89'])).
% 5.17/5.35  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('92', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('93', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(redefinition_k1_partfun1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.17/5.35     ( ( ( v1_funct_1 @ E ) & 
% 5.17/5.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.17/5.35         ( v1_funct_1 @ F ) & 
% 5.17/5.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.17/5.35       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.17/5.35  thf('94', plain,
% 5.17/5.35      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.17/5.35         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.17/5.35          | ~ (v1_funct_1 @ X44)
% 5.17/5.35          | ~ (v1_funct_1 @ X47)
% 5.17/5.35          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 5.17/5.35          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 5.17/5.35              = (k5_relat_1 @ X44 @ X47)))),
% 5.17/5.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.17/5.35  thf('95', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 5.17/5.35            = (k5_relat_1 @ sk_D @ X0))
% 5.17/5.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.17/5.35          | ~ (v1_funct_1 @ X0)
% 5.17/5.35          | ~ (v1_funct_1 @ sk_D))),
% 5.17/5.35      inference('sup-', [status(thm)], ['93', '94'])).
% 5.17/5.35  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('97', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 5.17/5.35            = (k5_relat_1 @ sk_D @ X0))
% 5.17/5.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.17/5.35          | ~ (v1_funct_1 @ X0))),
% 5.17/5.35      inference('demod', [status(thm)], ['95', '96'])).
% 5.17/5.35  thf('98', plain,
% 5.17/5.35      ((~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.17/5.35            = (k5_relat_1 @ sk_D @ sk_E)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['92', '97'])).
% 5.17/5.35  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('100', plain,
% 5.17/5.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.17/5.35         = (k5_relat_1 @ sk_D @ sk_E))),
% 5.17/5.35      inference('demod', [status(thm)], ['98', '99'])).
% 5.17/5.35  thf('101', plain,
% 5.17/5.35      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 5.17/5.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 5.17/5.35      inference('demod', [status(thm)], ['90', '91', '100'])).
% 5.17/5.35  thf(redefinition_k2_relset_1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.17/5.35  thf('102', plain,
% 5.17/5.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.17/5.35         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 5.17/5.35          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 5.17/5.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.17/5.35  thf('103', plain,
% 5.17/5.35      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 5.17/5.35         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['101', '102'])).
% 5.17/5.35  thf('104', plain,
% 5.17/5.35      (((k2_relset_1 @ sk_A @ sk_C @ 
% 5.17/5.35         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('105', plain,
% 5.17/5.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.17/5.35         = (k5_relat_1 @ sk_D @ sk_E))),
% 5.17/5.35      inference('demod', [status(thm)], ['98', '99'])).
% 5.17/5.35  thf('106', plain,
% 5.17/5.35      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.17/5.35      inference('demod', [status(thm)], ['104', '105'])).
% 5.17/5.35  thf('107', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.17/5.35      inference('sup+', [status(thm)], ['103', '106'])).
% 5.17/5.35  thf(t45_relat_1, axiom,
% 5.17/5.35    (![A:$i]:
% 5.17/5.35     ( ( v1_relat_1 @ A ) =>
% 5.17/5.35       ( ![B:$i]:
% 5.17/5.35         ( ( v1_relat_1 @ B ) =>
% 5.17/5.35           ( r1_tarski @
% 5.17/5.35             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.17/5.35  thf('108', plain,
% 5.17/5.35      (![X7 : $i, X8 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X7)
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 5.17/5.35             (k2_relat_1 @ X7))
% 5.17/5.35          | ~ (v1_relat_1 @ X8))),
% 5.17/5.35      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.17/5.35  thf('109', plain,
% 5.17/5.35      (![X0 : $i, X2 : $i]:
% 5.17/5.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.17/5.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.17/5.35  thf('110', plain,
% 5.17/5.35      (![X0 : $i, X1 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X1)
% 5.17/5.35          | ~ (v1_relat_1 @ X0)
% 5.17/5.35          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.17/5.35               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.17/5.35          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.17/5.35      inference('sup-', [status(thm)], ['108', '109'])).
% 5.17/5.35  thf('111', plain,
% 5.17/5.35      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 5.17/5.35        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_relat_1 @ sk_D))),
% 5.17/5.35      inference('sup-', [status(thm)], ['107', '110'])).
% 5.17/5.35  thf('112', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf(cc2_relset_1, axiom,
% 5.17/5.35    (![A:$i,B:$i,C:$i]:
% 5.17/5.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.17/5.35       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.17/5.35  thf('113', plain,
% 5.17/5.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.17/5.35         ((v5_relat_1 @ X21 @ X23)
% 5.17/5.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.17/5.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.17/5.35  thf('114', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 5.17/5.35      inference('sup-', [status(thm)], ['112', '113'])).
% 5.17/5.35  thf('115', plain,
% 5.17/5.35      (![X3 : $i, X4 : $i]:
% 5.17/5.35         (~ (v5_relat_1 @ X3 @ X4)
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.17/5.35          | ~ (v1_relat_1 @ X3))),
% 5.17/5.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.17/5.35  thf('116', plain,
% 5.17/5.35      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 5.17/5.35      inference('sup-', [status(thm)], ['114', '115'])).
% 5.17/5.35  thf('117', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('118', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 5.17/5.35      inference('demod', [status(thm)], ['116', '117'])).
% 5.17/5.35  thf('119', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.17/5.35      inference('sup+', [status(thm)], ['103', '106'])).
% 5.17/5.35  thf('120', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('121', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('122', plain,
% 5.17/5.35      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.17/5.35         ((v1_relat_1 @ X18)
% 5.17/5.35          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.17/5.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.17/5.35  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 5.17/5.35      inference('sup-', [status(thm)], ['121', '122'])).
% 5.17/5.35  thf('124', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 5.17/5.35      inference('demod', [status(thm)], ['111', '118', '119', '120', '123'])).
% 5.17/5.35  thf('125', plain, (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['83', '124'])).
% 5.17/5.35  thf('126', plain,
% 5.17/5.35      (![X14 : $i, X15 : $i]:
% 5.17/5.35         (~ (v2_funct_1 @ X14)
% 5.17/5.35          | ((k9_relat_1 @ X14 @ X15)
% 5.17/5.35              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 5.17/5.35          | ~ (v1_funct_1 @ X14)
% 5.17/5.35          | ~ (v1_relat_1 @ X14))),
% 5.17/5.35      inference('cnf', [status(esa)], [t154_funct_1])).
% 5.17/5.35  thf('127', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('128', plain,
% 5.17/5.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.17/5.35         ((v5_relat_1 @ X21 @ X23)
% 5.17/5.35          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.17/5.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.17/5.35  thf('129', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 5.17/5.35      inference('sup-', [status(thm)], ['127', '128'])).
% 5.17/5.35  thf('130', plain,
% 5.17/5.35      (![X3 : $i, X4 : $i]:
% 5.17/5.35         (~ (v5_relat_1 @ X3 @ X4)
% 5.17/5.35          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.17/5.35          | ~ (v1_relat_1 @ X3))),
% 5.17/5.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.17/5.35  thf('131', plain,
% 5.17/5.35      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 5.17/5.35      inference('sup-', [status(thm)], ['129', '130'])).
% 5.17/5.35  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 5.17/5.35      inference('sup-', [status(thm)], ['121', '122'])).
% 5.17/5.35  thf('133', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 5.17/5.35      inference('demod', [status(thm)], ['131', '132'])).
% 5.17/5.35  thf('134', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf('135', plain,
% 5.17/5.35      (![X11 : $i]:
% 5.17/5.35         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 5.17/5.35          | ~ (v2_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_funct_1 @ X11)
% 5.17/5.35          | ~ (v1_relat_1 @ X11))),
% 5.17/5.35      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.17/5.35  thf('136', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 5.17/5.35      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 5.17/5.35  thf('137', plain,
% 5.17/5.35      (![X12 : $i, X13 : $i]:
% 5.17/5.35         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 5.17/5.35          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 5.17/5.35          | ~ (v1_funct_1 @ X13)
% 5.17/5.35          | ~ (v1_relat_1 @ X13))),
% 5.17/5.35      inference('cnf', [status(esa)], [t147_funct_1])).
% 5.17/5.35  thf('138', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (r1_tarski @ X0 @ sk_B)
% 5.17/5.35          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['136', '137'])).
% 5.17/5.35  thf('139', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ sk_E)
% 5.17/5.35          | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35          | ~ (v2_funct_1 @ sk_E)
% 5.17/5.35          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0))
% 5.17/5.35          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35          | ~ (r1_tarski @ X0 @ sk_B))),
% 5.17/5.35      inference('sup-', [status(thm)], ['135', '138'])).
% 5.17/5.35  thf('140', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('141', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('142', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('143', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0))
% 5.17/5.35          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 5.17/5.35          | ~ (r1_tarski @ X0 @ sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 5.17/5.35  thf('144', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ sk_E)
% 5.17/5.35          | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35          | ~ (v2_funct_1 @ sk_E)
% 5.17/5.35          | ~ (r1_tarski @ X0 @ sk_B)
% 5.17/5.35          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 5.17/5.35      inference('sup-', [status(thm)], ['134', '143'])).
% 5.17/5.35  thf('145', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('146', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('147', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('148', plain,
% 5.17/5.35      (![X0 : $i]:
% 5.17/5.35         (~ (r1_tarski @ X0 @ sk_B)
% 5.17/5.35          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 5.17/5.35      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 5.17/5.35  thf('149', plain,
% 5.17/5.35      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35         (k10_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_D)))
% 5.17/5.35         = (k2_relat_1 @ sk_D))),
% 5.17/5.35      inference('sup-', [status(thm)], ['133', '148'])).
% 5.17/5.35  thf('150', plain,
% 5.17/5.35      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35          (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E)
% 5.17/5.35        | ~ (v1_funct_1 @ sk_E)
% 5.17/5.35        | ~ (v2_funct_1 @ sk_E))),
% 5.17/5.35      inference('sup+', [status(thm)], ['126', '149'])).
% 5.17/5.35  thf('151', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('153', plain, ((v2_funct_1 @ sk_E)),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('154', plain,
% 5.17/5.35      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.17/5.35         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))),
% 5.17/5.35      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 5.17/5.35  thf('155', plain,
% 5.17/5.35      (![X5 : $i, X6 : $i]:
% 5.17/5.35         (~ (v1_relat_1 @ X5)
% 5.17/5.35          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 5.17/5.35              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 5.17/5.35          | ~ (v1_relat_1 @ X6))),
% 5.17/5.35      inference('cnf', [status(esa)], [t160_relat_1])).
% 5.17/5.35  thf('156', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.17/5.35      inference('sup+', [status(thm)], ['103', '106'])).
% 5.17/5.35  thf('157', plain,
% 5.17/5.35      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 5.17/5.35        | ~ (v1_relat_1 @ sk_D)
% 5.17/5.35        | ~ (v1_relat_1 @ sk_E))),
% 5.17/5.35      inference('sup+', [status(thm)], ['155', '156'])).
% 5.17/5.35  thf('158', plain, ((v1_relat_1 @ sk_D)),
% 5.17/5.35      inference('sup-', [status(thm)], ['121', '122'])).
% 5.17/5.35  thf('159', plain, ((v1_relat_1 @ sk_E)),
% 5.17/5.35      inference('sup-', [status(thm)], ['33', '34'])).
% 5.17/5.35  thf('160', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 5.17/5.35      inference('demod', [status(thm)], ['157', '158', '159'])).
% 5.17/5.35  thf('161', plain,
% 5.17/5.35      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (k2_relat_1 @ sk_D))),
% 5.17/5.35      inference('demod', [status(thm)], ['154', '160'])).
% 5.17/5.35  thf('162', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 5.17/5.35      inference('sup+', [status(thm)], ['125', '161'])).
% 5.17/5.35  thf('163', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('164', plain,
% 5.17/5.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.17/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.35  thf('165', plain,
% 5.17/5.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.17/5.35         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 5.17/5.35          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 5.17/5.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.17/5.35  thf('166', plain,
% 5.17/5.35      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.17/5.35      inference('sup-', [status(thm)], ['164', '165'])).
% 5.17/5.35  thf('167', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 5.17/5.35      inference('demod', [status(thm)], ['163', '166'])).
% 5.17/5.35  thf('168', plain, ($false),
% 5.17/5.35      inference('simplify_reflect-', [status(thm)], ['162', '167'])).
% 5.17/5.35  
% 5.17/5.35  % SZS output end Refutation
% 5.17/5.35  
% 5.17/5.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
