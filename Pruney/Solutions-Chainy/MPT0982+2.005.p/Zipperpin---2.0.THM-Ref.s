%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zacvNiUyJv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:55 EST 2020

% Result     : Theorem 15.56s
% Output     : Refutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :  334 (7489 expanded)
%              Number of leaves         :   50 (2259 expanded)
%              Depth                    :   57
%              Number of atoms          : 2928 (140700 expanded)
%              Number of equality atoms :  163 (8693 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k10_relat_1 @ sk_E @ X0 ) )
      | ( ( k1_relat_1 @ sk_E )
        = ( k10_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k10_relat_1 @ sk_E @ X0 ) )
      | ( sk_B
        = ( k10_relat_1 @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_B
      = ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,
    ( sk_B
    = ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','25','27','28'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k9_relat_1 @ X7 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['36','39'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('46',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('51',plain,
    ( sk_B
    = ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','25','27','28'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('63',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k9_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('67',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k9_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('70',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('78',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k9_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_E ) )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['67','94'])).

thf('96',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('98',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['95','101','102','103','104'])).

thf('106',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) @ ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['66','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('110',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ sk_E @ ( k10_relat_1 @ sk_E @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('116',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_E @ ( k10_relat_1 @ sk_E @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_E @ ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['65','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['95','101','102','103','104'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('123',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ sk_E @ ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) ) )
        = ( k9_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_E @ ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) ) )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_E @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','130','131','132','133'])).

thf('135',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['64','134','135'])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('139',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['49','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('144',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['146','150'])).

thf('152',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['95','101','102','103','104'])).

thf('153',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('154',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('155',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('159',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['47','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('164',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['46','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('169',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_E ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['171','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('184',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('189',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['43','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('194',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_E @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','130','131','132','133'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('203',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('208',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','210'])).

thf('212',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['31','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('214',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['30','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('219',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('220',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k9_relat_1 @ X7 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('222',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['220','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('230',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('231',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('234',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('238',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('239',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
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

thf('242',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('243',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['240','245'])).

thf('247',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('249',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('250',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
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

thf('255',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['253','258'])).

thf('260',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['252','261'])).

thf('263',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('265',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('267',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('269',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['252','261'])).

thf('271',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['239','262','269','270'])).

thf('272',plain,
    ( sk_B
    = ( k10_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['29','271'])).

thf('273',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('274',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['252','261'])).

thf('275',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['272','275'])).

thf('277',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('280',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['277','280'])).

thf('282',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['276','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zacvNiUyJv
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.56/15.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.56/15.77  % Solved by: fo/fo7.sh
% 15.56/15.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.56/15.77  % done 9220 iterations in 15.307s
% 15.56/15.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.56/15.77  % SZS output start Refutation
% 15.56/15.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.56/15.77  thf(sk_C_type, type, sk_C: $i).
% 15.56/15.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.56/15.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.56/15.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.56/15.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 15.56/15.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 15.56/15.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.56/15.77  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 15.56/15.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.56/15.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.56/15.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.56/15.77  thf(sk_E_type, type, sk_E: $i).
% 15.56/15.77  thf(sk_D_type, type, sk_D: $i).
% 15.56/15.77  thf(sk_B_type, type, sk_B: $i).
% 15.56/15.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.56/15.77  thf(sk_A_type, type, sk_A: $i).
% 15.56/15.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.56/15.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.56/15.77  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 15.56/15.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.56/15.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 15.56/15.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 15.56/15.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.56/15.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.56/15.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 15.56/15.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.56/15.77  thf(t169_relat_1, axiom,
% 15.56/15.77    (![A:$i]:
% 15.56/15.77     ( ( v1_relat_1 @ A ) =>
% 15.56/15.77       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 15.56/15.77  thf('0', plain,
% 15.56/15.77      (![X11 : $i]:
% 15.56/15.77         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 15.56/15.77          | ~ (v1_relat_1 @ X11))),
% 15.56/15.77      inference('cnf', [status(esa)], [t169_relat_1])).
% 15.56/15.77  thf(t28_funct_2, conjecture,
% 15.56/15.77    (![A:$i,B:$i,C:$i,D:$i]:
% 15.56/15.77     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.56/15.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.56/15.77       ( ![E:$i]:
% 15.56/15.77         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 15.56/15.77             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.56/15.77           ( ( ( ( k2_relset_1 @
% 15.56/15.77                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 15.56/15.77                 ( C ) ) & 
% 15.56/15.77               ( v2_funct_1 @ E ) ) =>
% 15.56/15.77             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 15.56/15.77               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 15.56/15.77  thf(zf_stmt_0, negated_conjecture,
% 15.56/15.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.56/15.77        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.56/15.77            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.56/15.77          ( ![E:$i]:
% 15.56/15.77            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 15.56/15.77                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.56/15.77              ( ( ( ( k2_relset_1 @
% 15.56/15.77                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 15.56/15.77                    ( C ) ) & 
% 15.56/15.77                  ( v2_funct_1 @ E ) ) =>
% 15.56/15.77                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 15.56/15.77                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 15.56/15.77    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 15.56/15.77  thf('1', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(d1_funct_2, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.56/15.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.56/15.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.56/15.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.56/15.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.56/15.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.56/15.77  thf(zf_stmt_1, axiom,
% 15.56/15.77    (![C:$i,B:$i,A:$i]:
% 15.56/15.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.56/15.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.56/15.77  thf('2', plain,
% 15.56/15.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 15.56/15.77         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 15.56/15.77          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 15.56/15.77          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.56/15.77  thf('3', plain,
% 15.56/15.77      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 15.56/15.77        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['1', '2'])).
% 15.56/15.77  thf(zf_stmt_2, axiom,
% 15.56/15.77    (![B:$i,A:$i]:
% 15.56/15.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.56/15.77       ( zip_tseitin_0 @ B @ A ) ))).
% 15.56/15.77  thf('4', plain,
% 15.56/15.77      (![X31 : $i, X32 : $i]:
% 15.56/15.77         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 15.56/15.77  thf('5', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.56/15.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.56/15.77  thf(zf_stmt_5, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.56/15.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.56/15.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.56/15.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.56/15.77  thf('6', plain,
% 15.56/15.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.56/15.77         (~ (zip_tseitin_0 @ X36 @ X37)
% 15.56/15.77          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 15.56/15.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.56/15.77  thf('7', plain,
% 15.56/15.77      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 15.56/15.77      inference('sup-', [status(thm)], ['5', '6'])).
% 15.56/15.77  thf('8', plain,
% 15.56/15.77      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 15.56/15.77      inference('sup-', [status(thm)], ['4', '7'])).
% 15.56/15.77  thf('9', plain, (((sk_C) != (k1_xboole_0))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('10', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 15.56/15.77      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 15.56/15.77  thf('11', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(redefinition_k1_relset_1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.56/15.77  thf('12', plain,
% 15.56/15.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 15.56/15.77         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 15.56/15.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 15.56/15.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.56/15.77  thf('13', plain,
% 15.56/15.77      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('sup-', [status(thm)], ['11', '12'])).
% 15.56/15.77  thf('14', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['3', '10', '13'])).
% 15.56/15.77  thf(t167_relat_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( v1_relat_1 @ B ) =>
% 15.56/15.77       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 15.56/15.77  thf('15', plain,
% 15.56/15.77      (![X9 : $i, X10 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 15.56/15.77          | ~ (v1_relat_1 @ X9))),
% 15.56/15.77      inference('cnf', [status(esa)], [t167_relat_1])).
% 15.56/15.77  thf(d10_xboole_0, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.56/15.77  thf('16', plain,
% 15.56/15.77      (![X0 : $i, X2 : $i]:
% 15.56/15.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.77  thf('17', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 15.56/15.77          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['15', '16'])).
% 15.56/15.77  thf('18', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ sk_B @ (k10_relat_1 @ sk_E @ X0))
% 15.56/15.77          | ((k1_relat_1 @ sk_E) = (k10_relat_1 @ sk_E @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ sk_E))),
% 15.56/15.77      inference('sup-', [status(thm)], ['14', '17'])).
% 15.56/15.77  thf('19', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['3', '10', '13'])).
% 15.56/15.77  thf('20', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(cc1_relset_1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( v1_relat_1 @ C ) ))).
% 15.56/15.77  thf('21', plain,
% 15.56/15.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.56/15.77         ((v1_relat_1 @ X19)
% 15.56/15.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 15.56/15.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.56/15.77  thf('22', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('23', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ sk_B @ (k10_relat_1 @ sk_E @ X0))
% 15.56/15.77          | ((sk_B) = (k10_relat_1 @ sk_E @ X0)))),
% 15.56/15.77      inference('demod', [status(thm)], ['18', '19', '22'])).
% 15.56/15.77  thf('24', plain,
% 15.56/15.77      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_E))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ((sk_B) = (k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['0', '23'])).
% 15.56/15.77  thf('25', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['3', '10', '13'])).
% 15.56/15.77  thf('26', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 15.56/15.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.77  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.77      inference('simplify', [status(thm)], ['26'])).
% 15.56/15.77  thf('28', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('29', plain, (((sk_B) = (k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['24', '25', '27', '28'])).
% 15.56/15.77  thf(t160_relat_1, axiom,
% 15.56/15.77    (![A:$i]:
% 15.56/15.77     ( ( v1_relat_1 @ A ) =>
% 15.56/15.77       ( ![B:$i]:
% 15.56/15.77         ( ( v1_relat_1 @ B ) =>
% 15.56/15.77           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 15.56/15.77             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 15.56/15.77  thf('30', plain,
% 15.56/15.77      (![X7 : $i, X8 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X7)
% 15.56/15.77          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 15.56/15.77              = (k9_relat_1 @ X7 @ (k2_relat_1 @ X8)))
% 15.56/15.77          | ~ (v1_relat_1 @ X8))),
% 15.56/15.77      inference('cnf', [status(esa)], [t160_relat_1])).
% 15.56/15.77  thf(t155_funct_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.56/15.77       ( ( v2_funct_1 @ B ) =>
% 15.56/15.77         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 15.56/15.77  thf('31', plain,
% 15.56/15.77      (![X17 : $i, X18 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X17)
% 15.56/15.77          | ((k10_relat_1 @ X17 @ X18)
% 15.56/15.77              = (k9_relat_1 @ (k2_funct_1 @ X17) @ X18))
% 15.56/15.77          | ~ (v1_funct_1 @ X17)
% 15.56/15.77          | ~ (v1_relat_1 @ X17))),
% 15.56/15.77      inference('cnf', [status(esa)], [t155_funct_1])).
% 15.56/15.77  thf('32', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(cc2_relset_1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.56/15.77  thf('33', plain,
% 15.56/15.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.56/15.77         ((v5_relat_1 @ X22 @ X24)
% 15.56/15.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.56/15.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.56/15.77  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 15.56/15.77      inference('sup-', [status(thm)], ['32', '33'])).
% 15.56/15.77  thf(d19_relat_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( v1_relat_1 @ B ) =>
% 15.56/15.77       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 15.56/15.77  thf('35', plain,
% 15.56/15.77      (![X3 : $i, X4 : $i]:
% 15.56/15.77         (~ (v5_relat_1 @ X3 @ X4)
% 15.56/15.77          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 15.56/15.77          | ~ (v1_relat_1 @ X3))),
% 15.56/15.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 15.56/15.77  thf('36', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 15.56/15.77      inference('sup-', [status(thm)], ['34', '35'])).
% 15.56/15.77  thf('37', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('38', plain,
% 15.56/15.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.56/15.77         ((v1_relat_1 @ X19)
% 15.56/15.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 15.56/15.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.56/15.77  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 15.56/15.77      inference('sup-', [status(thm)], ['37', '38'])).
% 15.56/15.77  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 15.56/15.77      inference('demod', [status(thm)], ['36', '39'])).
% 15.56/15.77  thf(fc6_funct_1, axiom,
% 15.56/15.77    (![A:$i]:
% 15.56/15.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 15.56/15.77       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 15.56/15.77         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 15.56/15.77         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 15.56/15.77  thf('41', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('42', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('43', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('44', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('45', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('46', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('47', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('48', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('49', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('50', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('51', plain, (((sk_B) = (k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['24', '25', '27', '28'])).
% 15.56/15.77  thf('52', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('53', plain,
% 15.56/15.77      (![X17 : $i, X18 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X17)
% 15.56/15.77          | ((k10_relat_1 @ X17 @ X18)
% 15.56/15.77              = (k9_relat_1 @ (k2_funct_1 @ X17) @ X18))
% 15.56/15.77          | ~ (v1_funct_1 @ X17)
% 15.56/15.77          | ~ (v1_relat_1 @ X17))),
% 15.56/15.77      inference('cnf', [status(esa)], [t155_funct_1])).
% 15.56/15.77  thf(t144_relat_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( v1_relat_1 @ B ) =>
% 15.56/15.77       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 15.56/15.77  thf('54', plain,
% 15.56/15.77      (![X5 : $i, X6 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k2_relat_1 @ X5))
% 15.56/15.77          | ~ (v1_relat_1 @ X5))),
% 15.56/15.77      inference('cnf', [status(esa)], [t144_relat_1])).
% 15.56/15.77  thf('55', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 15.56/15.77           (k2_relat_1 @ (k2_funct_1 @ X1)))
% 15.56/15.77          | ~ (v1_relat_1 @ X1)
% 15.56/15.77          | ~ (v1_funct_1 @ X1)
% 15.56/15.77          | ~ (v2_funct_1 @ X1)
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 15.56/15.77      inference('sup+', [status(thm)], ['53', '54'])).
% 15.56/15.77  thf('56', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 15.56/15.77             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['52', '55'])).
% 15.56/15.77  thf('57', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 15.56/15.77           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['56'])).
% 15.56/15.77  thf('58', plain,
% 15.56/15.77      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['51', '57'])).
% 15.56/15.77  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('61', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('62', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 15.56/15.77  thf(t147_funct_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.56/15.77       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 15.56/15.77         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 15.56/15.77  thf('63', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('64', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 15.56/15.77            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ sk_B)) = (sk_B)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['62', '63'])).
% 15.56/15.77  thf(t154_funct_1, axiom,
% 15.56/15.77    (![A:$i,B:$i]:
% 15.56/15.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.56/15.77       ( ( v2_funct_1 @ B ) =>
% 15.56/15.77         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 15.56/15.77  thf('65', plain,
% 15.56/15.77      (![X15 : $i, X16 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X15)
% 15.56/15.77          | ((k9_relat_1 @ X15 @ X16)
% 15.56/15.77              = (k10_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 15.56/15.77          | ~ (v1_funct_1 @ X15)
% 15.56/15.77          | ~ (v1_relat_1 @ X15))),
% 15.56/15.77      inference('cnf', [status(esa)], [t154_funct_1])).
% 15.56/15.77  thf('66', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('67', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['3', '10', '13'])).
% 15.56/15.77  thf('68', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('69', plain,
% 15.56/15.77      (![X15 : $i, X16 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X15)
% 15.56/15.77          | ((k9_relat_1 @ X15 @ X16)
% 15.56/15.77              = (k10_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 15.56/15.77          | ~ (v1_funct_1 @ X15)
% 15.56/15.77          | ~ (v1_relat_1 @ X15))),
% 15.56/15.77      inference('cnf', [status(esa)], [t154_funct_1])).
% 15.56/15.77  thf('70', plain,
% 15.56/15.77      (![X11 : $i]:
% 15.56/15.77         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 15.56/15.77          | ~ (v1_relat_1 @ X11))),
% 15.56/15.77      inference('cnf', [status(esa)], [t169_relat_1])).
% 15.56/15.77  thf('71', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 15.56/15.77      inference('sup+', [status(thm)], ['69', '70'])).
% 15.56/15.77  thf('72', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['68', '71'])).
% 15.56/15.77  thf('73', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['72'])).
% 15.56/15.77  thf('74', plain,
% 15.56/15.77      (![X5 : $i, X6 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k2_relat_1 @ X5))
% 15.56/15.77          | ~ (v1_relat_1 @ X5))),
% 15.56/15.77      inference('cnf', [status(esa)], [t144_relat_1])).
% 15.56/15.77  thf('75', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('sup+', [status(thm)], ['73', '74'])).
% 15.56/15.77  thf('76', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['75'])).
% 15.56/15.77  thf('77', plain,
% 15.56/15.77      (![X11 : $i]:
% 15.56/15.77         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 15.56/15.77          | ~ (v1_relat_1 @ X11))),
% 15.56/15.77      inference('cnf', [status(esa)], [t169_relat_1])).
% 15.56/15.77  thf('78', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.77      inference('simplify', [status(thm)], ['26'])).
% 15.56/15.77  thf('79', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('80', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 15.56/15.77              = (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['78', '79'])).
% 15.56/15.77  thf('81', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('sup+', [status(thm)], ['77', '80'])).
% 15.56/15.77  thf('82', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['81'])).
% 15.56/15.77  thf('83', plain,
% 15.56/15.77      (![X12 : $i]:
% 15.56/15.77         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 15.56/15.77          | ~ (v2_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_funct_1 @ X12)
% 15.56/15.77          | ~ (v1_relat_1 @ X12))),
% 15.56/15.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 15.56/15.77  thf('84', plain,
% 15.56/15.77      (![X15 : $i, X16 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X15)
% 15.56/15.77          | ((k9_relat_1 @ X15 @ X16)
% 15.56/15.77              = (k10_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 15.56/15.77          | ~ (v1_funct_1 @ X15)
% 15.56/15.77          | ~ (v1_relat_1 @ X15))),
% 15.56/15.77      inference('cnf', [status(esa)], [t154_funct_1])).
% 15.56/15.77  thf('85', plain,
% 15.56/15.77      (![X9 : $i, X10 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 15.56/15.77          | ~ (v1_relat_1 @ X9))),
% 15.56/15.77      inference('cnf', [status(esa)], [t167_relat_1])).
% 15.56/15.77  thf('86', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 15.56/15.77           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 15.56/15.77          | ~ (v1_relat_1 @ X1)
% 15.56/15.77          | ~ (v1_funct_1 @ X1)
% 15.56/15.77          | ~ (v2_funct_1 @ X1)
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 15.56/15.77      inference('sup+', [status(thm)], ['84', '85'])).
% 15.56/15.77  thf('87', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 15.56/15.77             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['83', '86'])).
% 15.56/15.77  thf('88', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 15.56/15.77           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['87'])).
% 15.56/15.77  thf('89', plain,
% 15.56/15.77      (![X0 : $i, X2 : $i]:
% 15.56/15.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.77  thf('90', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 15.56/15.77               (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['88', '89'])).
% 15.56/15.77  thf('91', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 15.56/15.77              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('sup-', [status(thm)], ['82', '90'])).
% 15.56/15.77  thf('92', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X0)
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 15.56/15.77              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['91'])).
% 15.56/15.77  thf('93', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 15.56/15.77              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0))),
% 15.56/15.77      inference('sup-', [status(thm)], ['76', '92'])).
% 15.56/15.77  thf('94', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 15.56/15.77            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['93'])).
% 15.56/15.77  thf('95', plain,
% 15.56/15.77      ((((k1_relat_1 @ (k2_funct_1 @ sk_E)) = (k9_relat_1 @ sk_E @ sk_B))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['67', '94'])).
% 15.56/15.77  thf('96', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['3', '10', '13'])).
% 15.56/15.77  thf('97', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['81'])).
% 15.56/15.77  thf('98', plain,
% 15.56/15.77      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['96', '97'])).
% 15.56/15.77  thf('99', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('101', plain, (((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['98', '99', '100'])).
% 15.56/15.77  thf('102', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('104', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('105', plain,
% 15.56/15.77      (((k1_relat_1 @ (k2_funct_1 @ sk_E)) = (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['95', '101', '102', '103', '104'])).
% 15.56/15.77  thf('106', plain,
% 15.56/15.77      (![X9 : $i, X10 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 15.56/15.77          | ~ (v1_relat_1 @ X9))),
% 15.56/15.77      inference('cnf', [status(esa)], [t167_relat_1])).
% 15.56/15.77  thf('107', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0) @ 
% 15.56/15.77           (k2_relat_1 @ sk_E))
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('sup+', [status(thm)], ['105', '106'])).
% 15.56/15.77  thf('108', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0) @ 
% 15.56/15.77             (k2_relat_1 @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['66', '107'])).
% 15.56/15.77  thf('109', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('110', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('111', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('112', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0) @ 
% 15.56/15.77          (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 15.56/15.77  thf('113', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('114', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ((k9_relat_1 @ sk_E @ 
% 15.56/15.77              (k10_relat_1 @ sk_E @ (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)))
% 15.56/15.77              = (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['112', '113'])).
% 15.56/15.77  thf('115', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('116', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('117', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((k9_relat_1 @ sk_E @ 
% 15.56/15.77           (k10_relat_1 @ sk_E @ (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)))
% 15.56/15.77           = (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0))),
% 15.56/15.77      inference('demod', [status(thm)], ['114', '115', '116'])).
% 15.56/15.77  thf('118', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k9_relat_1 @ sk_E @ (k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)))
% 15.56/15.77            = (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ~ (v2_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['65', '117'])).
% 15.56/15.77  thf('119', plain,
% 15.56/15.77      (((k1_relat_1 @ (k2_funct_1 @ sk_E)) = (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['95', '101', '102', '103', '104'])).
% 15.56/15.77  thf('120', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 15.56/15.77           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['87'])).
% 15.56/15.77  thf('121', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (k2_relat_1 @ sk_E))
% 15.56/15.77          | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ~ (v2_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['119', '120'])).
% 15.56/15.77  thf('122', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('123', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('124', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('125', plain,
% 15.56/15.77      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 15.56/15.77  thf('126', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('127', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ((k9_relat_1 @ sk_E @ 
% 15.56/15.77              (k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)))
% 15.56/15.77              = (k9_relat_1 @ sk_E @ X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['125', '126'])).
% 15.56/15.77  thf('128', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('130', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((k9_relat_1 @ sk_E @ (k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)))
% 15.56/15.77           = (k9_relat_1 @ sk_E @ X0))),
% 15.56/15.77      inference('demod', [status(thm)], ['127', '128', '129'])).
% 15.56/15.77  thf('131', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('133', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('134', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((k9_relat_1 @ sk_E @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0))),
% 15.56/15.77      inference('demod', [status(thm)], ['118', '130', '131', '132', '133'])).
% 15.56/15.77  thf('135', plain, (((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['98', '99', '100'])).
% 15.56/15.77  thf('136', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B)))),
% 15.56/15.77      inference('demod', [status(thm)], ['64', '134', '135'])).
% 15.56/15.77  thf('137', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['50', '136'])).
% 15.56/15.77  thf('138', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('139', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('140', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('141', plain,
% 15.56/15.77      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 15.56/15.77  thf('142', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['49', '141'])).
% 15.56/15.77  thf('143', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('144', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('145', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('146', plain,
% 15.56/15.77      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 15.56/15.77  thf('147', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 15.56/15.77            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['93'])).
% 15.56/15.77  thf('148', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 15.56/15.77               (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['88', '89'])).
% 15.56/15.77  thf('149', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 15.56/15.77             (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('sup-', [status(thm)], ['147', '148'])).
% 15.56/15.77  thf('150', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 15.56/15.77               (k9_relat_1 @ X0 @ X1)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['149'])).
% 15.56/15.77  thf('151', plain,
% 15.56/15.77      ((~ (r1_tarski @ 
% 15.56/15.77           (k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 15.56/15.77            (k1_relat_1 @ (k2_funct_1 @ sk_E))) @ 
% 15.56/15.77           sk_B)
% 15.56/15.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E)))
% 15.56/15.77            = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['146', '150'])).
% 15.56/15.77  thf('152', plain,
% 15.56/15.77      (((k1_relat_1 @ (k2_funct_1 @ sk_E)) = (k2_relat_1 @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['95', '101', '102', '103', '104'])).
% 15.56/15.77  thf('153', plain,
% 15.56/15.77      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 15.56/15.77  thf('154', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.77      inference('simplify', [status(thm)], ['26'])).
% 15.56/15.77  thf('155', plain,
% 15.56/15.77      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 15.56/15.77  thf('156', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B)))),
% 15.56/15.77      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 15.56/15.77  thf('157', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B))
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['48', '156'])).
% 15.56/15.77  thf('158', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('159', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('160', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('161', plain,
% 15.56/15.77      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B))
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 15.56/15.77  thf('162', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['47', '161'])).
% 15.56/15.77  thf('163', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('164', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('165', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('166', plain,
% 15.56/15.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B)))),
% 15.56/15.77      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 15.56/15.77  thf('167', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['46', '166'])).
% 15.56/15.77  thf('168', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('169', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('170', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('171', plain,
% 15.56/15.77      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_E))) = (sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 15.56/15.77  thf('172', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['75'])).
% 15.56/15.77  thf('173', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 15.56/15.77              = (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['78', '79'])).
% 15.56/15.77  thf('174', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 15.56/15.77           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['87'])).
% 15.56/15.77  thf('175', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0))),
% 15.56/15.77      inference('sup+', [status(thm)], ['173', '174'])).
% 15.56/15.77  thf('176', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 15.56/15.77      inference('simplify', [status(thm)], ['175'])).
% 15.56/15.77  thf('177', plain,
% 15.56/15.77      (![X0 : $i, X2 : $i]:
% 15.56/15.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.77  thf('178', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['176', '177'])).
% 15.56/15.77  thf('179', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0))),
% 15.56/15.77      inference('sup-', [status(thm)], ['172', '178'])).
% 15.56/15.77  thf('180', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v2_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('simplify', [status(thm)], ['179'])).
% 15.56/15.77  thf('181', plain,
% 15.56/15.77      ((((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 15.56/15.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('sup+', [status(thm)], ['171', '180'])).
% 15.56/15.77  thf('182', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['45', '181'])).
% 15.56/15.77  thf('183', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('184', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('185', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('186', plain,
% 15.56/15.77      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E))))),
% 15.56/15.77      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 15.56/15.77  thf('187', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['44', '186'])).
% 15.56/15.77  thf('188', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('189', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('190', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('191', plain,
% 15.56/15.77      ((((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 15.56/15.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 15.56/15.77  thf('192', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['43', '191'])).
% 15.56/15.77  thf('193', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('194', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('195', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('196', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 15.56/15.77  thf('197', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('198', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X0 @ sk_B)
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 15.56/15.77              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['196', '197'])).
% 15.56/15.77  thf('199', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         ((k9_relat_1 @ sk_E @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0))),
% 15.56/15.77      inference('demod', [status(thm)], ['118', '130', '131', '132', '133'])).
% 15.56/15.77  thf('200', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X0 @ sk_B)
% 15.56/15.77          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 15.56/15.77              = (X0)))),
% 15.56/15.77      inference('demod', [status(thm)], ['198', '199'])).
% 15.56/15.77  thf('201', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 15.56/15.77              = (X0))
% 15.56/15.77          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ~ (r1_tarski @ X0 @ sk_B))),
% 15.56/15.77      inference('sup-', [status(thm)], ['42', '200'])).
% 15.56/15.77  thf('202', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('203', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('204', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('205', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 15.56/15.77          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 15.56/15.77          | ~ (r1_tarski @ X0 @ sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 15.56/15.77  thf('206', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ sk_E)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77          | ~ (v2_funct_1 @ sk_E)
% 15.56/15.77          | ~ (r1_tarski @ X0 @ sk_B)
% 15.56/15.77          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 15.56/15.77              = (X0)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['41', '205'])).
% 15.56/15.77  thf('207', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('208', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('209', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('210', plain,
% 15.56/15.77      (![X0 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X0 @ sk_B)
% 15.56/15.77          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 15.56/15.77              = (X0)))),
% 15.56/15.77      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 15.56/15.77  thf('211', plain,
% 15.56/15.77      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 15.56/15.77         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('sup-', [status(thm)], ['40', '210'])).
% 15.56/15.77  thf('212', plain,
% 15.56/15.77      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 15.56/15.77          = (k2_relat_1 @ sk_D))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ~ (v2_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['31', '211'])).
% 15.56/15.77  thf('213', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('214', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('215', plain, ((v2_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('216', plain,
% 15.56/15.77      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 15.56/15.77         = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('demod', [status(thm)], ['212', '213', '214', '215'])).
% 15.56/15.77  thf('217', plain,
% 15.56/15.77      ((((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77          = (k2_relat_1 @ sk_D))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_D)
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['30', '216'])).
% 15.56/15.77  thf('218', plain, ((v1_relat_1 @ sk_D)),
% 15.56/15.77      inference('sup-', [status(thm)], ['37', '38'])).
% 15.56/15.77  thf('219', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('220', plain,
% 15.56/15.77      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77         = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('demod', [status(thm)], ['217', '218', '219'])).
% 15.56/15.77  thf('221', plain,
% 15.56/15.77      (![X7 : $i, X8 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X7)
% 15.56/15.77          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 15.56/15.77              = (k9_relat_1 @ X7 @ (k2_relat_1 @ X8)))
% 15.56/15.77          | ~ (v1_relat_1 @ X8))),
% 15.56/15.77      inference('cnf', [status(esa)], [t160_relat_1])).
% 15.56/15.77  thf('222', plain,
% 15.56/15.77      (![X5 : $i, X6 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k2_relat_1 @ X5))
% 15.56/15.77          | ~ (v1_relat_1 @ X5))),
% 15.56/15.77      inference('cnf', [status(esa)], [t144_relat_1])).
% 15.56/15.77  thf('223', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 15.56/15.77           (k2_relat_1 @ X0))
% 15.56/15.77          | ~ (v1_relat_1 @ X1)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0))),
% 15.56/15.77      inference('sup+', [status(thm)], ['221', '222'])).
% 15.56/15.77  thf('224', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X1)
% 15.56/15.77          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 15.56/15.77             (k2_relat_1 @ X0)))),
% 15.56/15.77      inference('simplify', [status(thm)], ['223'])).
% 15.56/15.77  thf('225', plain,
% 15.56/15.77      (![X13 : $i, X14 : $i]:
% 15.56/15.77         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 15.56/15.77          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 15.56/15.77          | ~ (v1_funct_1 @ X14)
% 15.56/15.77          | ~ (v1_relat_1 @ X14))),
% 15.56/15.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 15.56/15.77  thf('226', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X1)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ((k9_relat_1 @ X0 @ 
% 15.56/15.77              (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 15.56/15.77              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['224', '225'])).
% 15.56/15.77  thf('227', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (((k9_relat_1 @ X0 @ 
% 15.56/15.77            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 15.56/15.77            = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (v1_relat_1 @ X1))),
% 15.56/15.77      inference('simplify', [status(thm)], ['226'])).
% 15.56/15.77  thf('228', plain,
% 15.56/15.77      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))
% 15.56/15.77          = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_D)
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E)
% 15.56/15.77        | ~ (v1_funct_1 @ sk_E))),
% 15.56/15.77      inference('sup+', [status(thm)], ['220', '227'])).
% 15.56/15.77  thf('229', plain, ((v1_relat_1 @ sk_D)),
% 15.56/15.77      inference('sup-', [status(thm)], ['37', '38'])).
% 15.56/15.77  thf('230', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('231', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('232', plain,
% 15.56/15.77      (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))
% 15.56/15.77         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 15.56/15.77  thf('233', plain,
% 15.56/15.77      (![X5 : $i, X6 : $i]:
% 15.56/15.77         ((r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k2_relat_1 @ X5))
% 15.56/15.77          | ~ (v1_relat_1 @ X5))),
% 15.56/15.77      inference('cnf', [status(esa)], [t144_relat_1])).
% 15.56/15.77  thf('234', plain,
% 15.56/15.77      (![X0 : $i, X2 : $i]:
% 15.56/15.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.77  thf('235', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i]:
% 15.56/15.77         (~ (v1_relat_1 @ X0)
% 15.56/15.77          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 15.56/15.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['233', '234'])).
% 15.56/15.77  thf('236', plain,
% 15.56/15.77      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 15.56/15.77           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77        | ((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 15.56/15.77        | ~ (v1_relat_1 @ sk_E))),
% 15.56/15.77      inference('sup-', [status(thm)], ['232', '235'])).
% 15.56/15.77  thf('237', plain,
% 15.56/15.77      (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))
% 15.56/15.77         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 15.56/15.77      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 15.56/15.77  thf('238', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('239', plain,
% 15.56/15.77      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 15.56/15.77           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))))),
% 15.56/15.77      inference('demod', [status(thm)], ['236', '237', '238'])).
% 15.56/15.77  thf('240', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('241', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(dt_k1_partfun1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.56/15.77     ( ( ( v1_funct_1 @ E ) & 
% 15.56/15.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.56/15.77         ( v1_funct_1 @ F ) & 
% 15.56/15.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 15.56/15.77       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 15.56/15.77         ( m1_subset_1 @
% 15.56/15.77           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 15.56/15.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 15.56/15.77  thf('242', plain,
% 15.56/15.77      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 15.56/15.77         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 15.56/15.77          | ~ (v1_funct_1 @ X39)
% 15.56/15.77          | ~ (v1_funct_1 @ X42)
% 15.56/15.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 15.56/15.77          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 15.56/15.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 15.56/15.77      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 15.56/15.77  thf('243', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.77         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 15.56/15.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 15.56/15.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 15.56/15.77          | ~ (v1_funct_1 @ X1)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_D))),
% 15.56/15.77      inference('sup-', [status(thm)], ['241', '242'])).
% 15.56/15.77  thf('244', plain, ((v1_funct_1 @ sk_D)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('245', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.77         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 15.56/15.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 15.56/15.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 15.56/15.77          | ~ (v1_funct_1 @ X1))),
% 15.56/15.77      inference('demod', [status(thm)], ['243', '244'])).
% 15.56/15.77  thf('246', plain,
% 15.56/15.77      ((~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | (m1_subset_1 @ 
% 15.56/15.77           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 15.56/15.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 15.56/15.77      inference('sup-', [status(thm)], ['240', '245'])).
% 15.56/15.77  thf('247', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('248', plain,
% 15.56/15.77      ((m1_subset_1 @ 
% 15.56/15.77        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 15.56/15.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 15.56/15.77      inference('demod', [status(thm)], ['246', '247'])).
% 15.56/15.77  thf(redefinition_k2_relset_1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i]:
% 15.56/15.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.56/15.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 15.56/15.77  thf('249', plain,
% 15.56/15.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.56/15.77         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 15.56/15.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 15.56/15.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 15.56/15.77  thf('250', plain,
% 15.56/15.77      (((k2_relset_1 @ sk_A @ sk_C @ 
% 15.56/15.77         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 15.56/15.77         = (k2_relat_1 @ 
% 15.56/15.77            (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['248', '249'])).
% 15.56/15.77  thf('251', plain,
% 15.56/15.77      (((k2_relset_1 @ sk_A @ sk_C @ 
% 15.56/15.77         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('252', plain,
% 15.56/15.77      (((k2_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 15.56/15.77         = (sk_C))),
% 15.56/15.77      inference('sup+', [status(thm)], ['250', '251'])).
% 15.56/15.77  thf('253', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('254', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf(redefinition_k1_partfun1, axiom,
% 15.56/15.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.56/15.77     ( ( ( v1_funct_1 @ E ) & 
% 15.56/15.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.56/15.77         ( v1_funct_1 @ F ) & 
% 15.56/15.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 15.56/15.77       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 15.56/15.77  thf('255', plain,
% 15.56/15.77      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 15.56/15.77         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 15.56/15.77          | ~ (v1_funct_1 @ X45)
% 15.56/15.77          | ~ (v1_funct_1 @ X48)
% 15.56/15.77          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 15.56/15.77          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 15.56/15.77              = (k5_relat_1 @ X45 @ X48)))),
% 15.56/15.77      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 15.56/15.77  thf('256', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.77         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 15.56/15.77            = (k5_relat_1 @ sk_D @ X0))
% 15.56/15.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 15.56/15.77          | ~ (v1_funct_1 @ X0)
% 15.56/15.77          | ~ (v1_funct_1 @ sk_D))),
% 15.56/15.77      inference('sup-', [status(thm)], ['254', '255'])).
% 15.56/15.77  thf('257', plain, ((v1_funct_1 @ sk_D)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('258', plain,
% 15.56/15.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.77         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 15.56/15.77            = (k5_relat_1 @ sk_D @ X0))
% 15.56/15.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 15.56/15.77          | ~ (v1_funct_1 @ X0))),
% 15.56/15.77      inference('demod', [status(thm)], ['256', '257'])).
% 15.56/15.77  thf('259', plain,
% 15.56/15.77      ((~ (v1_funct_1 @ sk_E)
% 15.56/15.77        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 15.56/15.77            = (k5_relat_1 @ sk_D @ sk_E)))),
% 15.56/15.77      inference('sup-', [status(thm)], ['253', '258'])).
% 15.56/15.77  thf('260', plain, ((v1_funct_1 @ sk_E)),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('261', plain,
% 15.56/15.77      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 15.56/15.77         = (k5_relat_1 @ sk_D @ sk_E))),
% 15.56/15.77      inference('demod', [status(thm)], ['259', '260'])).
% 15.56/15.77  thf('262', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 15.56/15.77      inference('demod', [status(thm)], ['252', '261'])).
% 15.56/15.77  thf('263', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('264', plain,
% 15.56/15.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.56/15.77         ((v5_relat_1 @ X22 @ X24)
% 15.56/15.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.56/15.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.56/15.77  thf('265', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 15.56/15.77      inference('sup-', [status(thm)], ['263', '264'])).
% 15.56/15.77  thf('266', plain,
% 15.56/15.77      (![X3 : $i, X4 : $i]:
% 15.56/15.77         (~ (v5_relat_1 @ X3 @ X4)
% 15.56/15.77          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 15.56/15.77          | ~ (v1_relat_1 @ X3))),
% 15.56/15.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 15.56/15.77  thf('267', plain,
% 15.56/15.77      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 15.56/15.77      inference('sup-', [status(thm)], ['265', '266'])).
% 15.56/15.77  thf('268', plain, ((v1_relat_1 @ sk_E)),
% 15.56/15.77      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.77  thf('269', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 15.56/15.77      inference('demod', [status(thm)], ['267', '268'])).
% 15.56/15.77  thf('270', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 15.56/15.77      inference('demod', [status(thm)], ['252', '261'])).
% 15.56/15.77  thf('271', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 15.56/15.77      inference('demod', [status(thm)], ['239', '262', '269', '270'])).
% 15.56/15.77  thf('272', plain, (((sk_B) = (k10_relat_1 @ sk_E @ sk_C))),
% 15.56/15.77      inference('demod', [status(thm)], ['29', '271'])).
% 15.56/15.77  thf('273', plain,
% 15.56/15.77      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 15.56/15.77         = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('demod', [status(thm)], ['217', '218', '219'])).
% 15.56/15.77  thf('274', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 15.56/15.77      inference('demod', [status(thm)], ['252', '261'])).
% 15.56/15.77  thf('275', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('demod', [status(thm)], ['273', '274'])).
% 15.56/15.77  thf('276', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('sup+', [status(thm)], ['272', '275'])).
% 15.56/15.77  thf('277', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('278', plain,
% 15.56/15.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.56/15.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.77  thf('279', plain,
% 15.56/15.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.56/15.77         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 15.56/15.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 15.56/15.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 15.56/15.77  thf('280', plain,
% 15.56/15.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 15.56/15.77      inference('sup-', [status(thm)], ['278', '279'])).
% 15.56/15.77  thf('281', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 15.56/15.77      inference('demod', [status(thm)], ['277', '280'])).
% 15.56/15.77  thf('282', plain, ($false),
% 15.56/15.77      inference('simplify_reflect-', [status(thm)], ['276', '281'])).
% 15.56/15.77  
% 15.56/15.77  % SZS output end Refutation
% 15.56/15.77  
% 15.56/15.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
