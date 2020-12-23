%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hMRAEnU8JK

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:33 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 164 expanded)
%              Number of leaves         :   43 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  902 (2518 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t172_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                     => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                      <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                       => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                        <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t172_funct_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('16',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','27'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X19 @ X18 ) @ X20 )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ~ ( r1_tarski @ sk_D @ sk_A ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k10_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('50',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf('51',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k9_relat_1 @ X15 @ X13 ) @ ( k9_relat_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hMRAEnU8JK
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.34/1.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.34/1.62  % Solved by: fo/fo7.sh
% 1.34/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.62  % done 1125 iterations in 1.159s
% 1.34/1.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.34/1.62  % SZS output start Refutation
% 1.34/1.62  thf(sk_D_type, type, sk_D: $i).
% 1.34/1.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.34/1.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.34/1.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.34/1.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.34/1.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.34/1.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.34/1.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.34/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.34/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.34/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.34/1.62  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.34/1.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.34/1.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.34/1.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.34/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.34/1.62  thf(sk_B_type, type, sk_B: $i > $i).
% 1.34/1.62  thf(sk_C_type, type, sk_C: $i).
% 1.34/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.34/1.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.34/1.62  thf(sk_E_type, type, sk_E: $i).
% 1.34/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.34/1.62  thf(t172_funct_2, conjecture,
% 1.34/1.62    (![A:$i]:
% 1.34/1.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.34/1.62       ( ![B:$i]:
% 1.34/1.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.34/1.62           ( ![C:$i]:
% 1.34/1.62             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.62               ( ![D:$i]:
% 1.34/1.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.34/1.62                   ( ![E:$i]:
% 1.34/1.62                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.34/1.62                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.34/1.62                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.34/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.62    (~( ![A:$i]:
% 1.34/1.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.34/1.62          ( ![B:$i]:
% 1.34/1.62            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.34/1.62              ( ![C:$i]:
% 1.34/1.62                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.62                    ( m1_subset_1 @
% 1.34/1.62                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.62                  ( ![D:$i]:
% 1.34/1.62                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.34/1.62                      ( ![E:$i]:
% 1.34/1.62                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.34/1.62                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.34/1.62                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.34/1.62    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 1.34/1.62  thf('0', plain,
% 1.34/1.62      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 1.34/1.62        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('1', plain,
% 1.34/1.62      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))) | 
% 1.34/1.62       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('split', [status(esa)], ['0'])).
% 1.34/1.62  thf('2', plain,
% 1.34/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(redefinition_k7_relset_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.34/1.62  thf('3', plain,
% 1.34/1.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.62         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.34/1.62          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 1.34/1.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.34/1.62  thf('4', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.34/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.34/1.62  thf('5', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 1.34/1.62        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('6', plain,
% 1.34/1.62      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 1.34/1.62         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('split', [status(esa)], ['5'])).
% 1.34/1.62  thf('7', plain,
% 1.34/1.62      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.34/1.62         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['4', '6'])).
% 1.34/1.62  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(d1_funct_2, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.34/1.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.34/1.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.34/1.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.34/1.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.34/1.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.34/1.62  thf(zf_stmt_1, axiom,
% 1.34/1.62    (![C:$i,B:$i,A:$i]:
% 1.34/1.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.34/1.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.34/1.62  thf('9', plain,
% 1.34/1.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.34/1.62         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 1.34/1.62          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 1.34/1.62          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.34/1.62  thf('10', plain,
% 1.34/1.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.34/1.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['8', '9'])).
% 1.34/1.62  thf('11', plain,
% 1.34/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(redefinition_k1_relset_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.34/1.62  thf('12', plain,
% 1.34/1.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.34/1.62         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.34/1.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.34/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.34/1.62  thf('13', plain,
% 1.34/1.62      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.34/1.62      inference('sup-', [status(thm)], ['11', '12'])).
% 1.34/1.62  thf('14', plain,
% 1.34/1.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.34/1.62        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.34/1.62      inference('demod', [status(thm)], ['10', '13'])).
% 1.34/1.62  thf('15', plain,
% 1.34/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.34/1.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.34/1.62  thf(zf_stmt_4, axiom,
% 1.34/1.62    (![B:$i,A:$i]:
% 1.34/1.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.34/1.62       ( zip_tseitin_0 @ B @ A ) ))).
% 1.34/1.62  thf(zf_stmt_5, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.34/1.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.34/1.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.34/1.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.34/1.62  thf('16', plain,
% 1.34/1.62      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.34/1.62         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.34/1.62          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.34/1.62          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.34/1.62  thf('17', plain,
% 1.34/1.62      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.34/1.62        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.34/1.62      inference('sup-', [status(thm)], ['15', '16'])).
% 1.34/1.62  thf('18', plain,
% 1.34/1.62      (![X43 : $i, X44 : $i]:
% 1.34/1.62         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.34/1.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.34/1.62  thf('19', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.34/1.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.34/1.62  thf('20', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.34/1.62      inference('sup+', [status(thm)], ['18', '19'])).
% 1.34/1.62  thf(d1_xboole_0, axiom,
% 1.34/1.62    (![A:$i]:
% 1.34/1.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.34/1.62  thf('21', plain,
% 1.34/1.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.34/1.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.34/1.62  thf(t7_ordinal1, axiom,
% 1.34/1.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.34/1.62  thf('22', plain,
% 1.34/1.62      (![X21 : $i, X22 : $i]:
% 1.34/1.62         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 1.34/1.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.34/1.62  thf('23', plain,
% 1.34/1.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['21', '22'])).
% 1.34/1.62  thf('24', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 1.34/1.62      inference('sup-', [status(thm)], ['20', '23'])).
% 1.34/1.62  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('26', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.34/1.62      inference('sup-', [status(thm)], ['24', '25'])).
% 1.34/1.62  thf('27', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 1.34/1.62      inference('demod', [status(thm)], ['17', '26'])).
% 1.34/1.62  thf('28', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.34/1.62      inference('demod', [status(thm)], ['14', '27'])).
% 1.34/1.62  thf(t163_funct_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.34/1.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.34/1.62           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.34/1.62         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.34/1.62  thf('29', plain,
% 1.34/1.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 1.34/1.62          | ~ (r1_tarski @ (k9_relat_1 @ X19 @ X18) @ X20)
% 1.34/1.62          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ X20))
% 1.34/1.62          | ~ (v1_funct_1 @ X19)
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.34/1.62  thf('30', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X0 @ sk_A)
% 1.34/1.62          | ~ (v1_relat_1 @ sk_C)
% 1.34/1.62          | ~ (v1_funct_1 @ sk_C)
% 1.34/1.62          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 1.34/1.62          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 1.34/1.62      inference('sup-', [status(thm)], ['28', '29'])).
% 1.34/1.62  thf('31', plain,
% 1.34/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(cc1_relset_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( v1_relat_1 @ C ) ))).
% 1.34/1.62  thf('32', plain,
% 1.34/1.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.62         ((v1_relat_1 @ X23)
% 1.34/1.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.34/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.34/1.62  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.62      inference('sup-', [status(thm)], ['31', '32'])).
% 1.34/1.62  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('35', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X0 @ sk_A)
% 1.34/1.62          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 1.34/1.62          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['30', '33', '34'])).
% 1.34/1.62  thf('36', plain,
% 1.34/1.62      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.34/1.62         | ~ (r1_tarski @ sk_D @ sk_A)))
% 1.34/1.62         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['7', '35'])).
% 1.34/1.62  thf('37', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(t3_subset, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.34/1.62  thf('38', plain,
% 1.34/1.62      (![X10 : $i, X11 : $i]:
% 1.34/1.62         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.34/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.34/1.62  thf('39', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.34/1.62      inference('sup-', [status(thm)], ['37', '38'])).
% 1.34/1.62  thf('40', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.34/1.62         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('demod', [status(thm)], ['36', '39'])).
% 1.34/1.62  thf('41', plain,
% 1.34/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf(redefinition_k8_relset_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.62       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.34/1.62  thf('42', plain,
% 1.34/1.62      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.34/1.62         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.34/1.62          | ((k8_relset_1 @ X34 @ X35 @ X33 @ X36) = (k10_relat_1 @ X33 @ X36)))),
% 1.34/1.62      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.34/1.62  thf('43', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.34/1.62      inference('sup-', [status(thm)], ['41', '42'])).
% 1.34/1.62  thf('44', plain,
% 1.34/1.62      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.34/1.62         <= (~
% 1.34/1.62             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('split', [status(esa)], ['0'])).
% 1.34/1.62  thf('45', plain,
% 1.34/1.62      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.34/1.62         <= (~
% 1.34/1.62             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['43', '44'])).
% 1.34/1.62  thf('46', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))) | 
% 1.34/1.62       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('sup-', [status(thm)], ['40', '45'])).
% 1.34/1.62  thf('47', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))) | 
% 1.34/1.62       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('split', [status(esa)], ['5'])).
% 1.34/1.62  thf(t145_funct_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.34/1.62       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.34/1.62  thf('48', plain,
% 1.34/1.62      (![X16 : $i, X17 : $i]:
% 1.34/1.62         ((r1_tarski @ (k9_relat_1 @ X16 @ (k10_relat_1 @ X16 @ X17)) @ X17)
% 1.34/1.62          | ~ (v1_funct_1 @ X16)
% 1.34/1.62          | ~ (v1_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.34/1.62  thf('49', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.34/1.62      inference('sup-', [status(thm)], ['41', '42'])).
% 1.34/1.62  thf('50', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('split', [status(esa)], ['5'])).
% 1.34/1.62  thf('51', plain,
% 1.34/1.62      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('sup+', [status(thm)], ['49', '50'])).
% 1.34/1.62  thf(t156_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ C ) =>
% 1.34/1.62       ( ( r1_tarski @ A @ B ) =>
% 1.34/1.62         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.34/1.62  thf('52', plain,
% 1.34/1.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X13 @ X14)
% 1.34/1.62          | ~ (v1_relat_1 @ X15)
% 1.34/1.62          | (r1_tarski @ (k9_relat_1 @ X15 @ X13) @ (k9_relat_1 @ X15 @ X14)))),
% 1.34/1.62      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.34/1.62  thf('53', plain,
% 1.34/1.62      ((![X0 : $i]:
% 1.34/1.62          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.34/1.62            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.34/1.62           | ~ (v1_relat_1 @ X0)))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['51', '52'])).
% 1.34/1.62  thf(t1_xboole_1, axiom,
% 1.34/1.62    (![A:$i,B:$i,C:$i]:
% 1.34/1.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.34/1.62       ( r1_tarski @ A @ C ) ))).
% 1.34/1.62  thf('54', plain,
% 1.34/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.34/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.34/1.62          | (r1_tarski @ X3 @ X5))),
% 1.34/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.34/1.62  thf('55', plain,
% 1.34/1.62      ((![X0 : $i, X1 : $i]:
% 1.34/1.62          (~ (v1_relat_1 @ X0)
% 1.34/1.62           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 1.34/1.62           | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ 
% 1.34/1.62                X1)))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['53', '54'])).
% 1.34/1.62  thf('56', plain,
% 1.34/1.62      (((~ (v1_relat_1 @ sk_C)
% 1.34/1.62         | ~ (v1_funct_1 @ sk_C)
% 1.34/1.62         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 1.34/1.62         | ~ (v1_relat_1 @ sk_C)))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['48', '55'])).
% 1.34/1.62  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.62      inference('sup-', [status(thm)], ['31', '32'])).
% 1.34/1.62  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.62      inference('sup-', [status(thm)], ['31', '32'])).
% 1.34/1.62  thf('60', plain,
% 1.34/1.62      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.34/1.62         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.34/1.62      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 1.34/1.62  thf('61', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.34/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.34/1.62  thf('62', plain,
% 1.34/1.62      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 1.34/1.62         <= (~
% 1.34/1.62             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('split', [status(esa)], ['0'])).
% 1.34/1.62  thf('63', plain,
% 1.34/1.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.34/1.62         <= (~
% 1.34/1.62             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['61', '62'])).
% 1.34/1.62  thf('64', plain,
% 1.34/1.62      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))) | 
% 1.34/1.62       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.34/1.62      inference('sup-', [status(thm)], ['60', '63'])).
% 1.34/1.62  thf('65', plain, ($false),
% 1.34/1.62      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '64'])).
% 1.34/1.62  
% 1.34/1.62  % SZS output end Refutation
% 1.34/1.62  
% 1.45/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
