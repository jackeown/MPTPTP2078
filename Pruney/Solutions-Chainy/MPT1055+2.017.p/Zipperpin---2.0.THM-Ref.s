%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYAr5f5Vmp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:36 EST 2020

% Result     : Theorem 6.76s
% Output     : Refutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 295 expanded)
%              Number of leaves         :   45 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  929 (4563 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('34',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['23','38'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X20 @ X19 ) @ X21 )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ~ ( r1_tarski @ sk_D @ sk_A ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['10','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['5','56'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('59',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('62',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['54'])).

thf('64',plain,(
    r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k9_relat_1 @ X16 @ X14 ) @ ( k9_relat_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['57','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYAr5f5Vmp
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.76/7.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.76/7.00  % Solved by: fo/fo7.sh
% 6.76/7.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.76/7.00  % done 2434 iterations in 6.535s
% 6.76/7.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.76/7.00  % SZS output start Refutation
% 6.76/7.00  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.76/7.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.76/7.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.76/7.00  thf(sk_D_type, type, sk_D: $i).
% 6.76/7.00  thf(sk_C_type, type, sk_C: $i).
% 6.76/7.00  thf(sk_E_type, type, sk_E: $i).
% 6.76/7.00  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.76/7.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.76/7.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.76/7.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.76/7.00  thf(sk_A_type, type, sk_A: $i).
% 6.76/7.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.76/7.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.76/7.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.76/7.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.76/7.00  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.76/7.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.76/7.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.76/7.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.76/7.00  thf(sk_B_type, type, sk_B: $i > $i).
% 6.76/7.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.76/7.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.76/7.00  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 6.76/7.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.76/7.00  thf(t172_funct_2, conjecture,
% 6.76/7.00    (![A:$i]:
% 6.76/7.00     ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.76/7.00       ( ![B:$i]:
% 6.76/7.00         ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.76/7.00           ( ![C:$i]:
% 6.76/7.00             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.76/7.00                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.76/7.00               ( ![D:$i]:
% 6.76/7.00                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 6.76/7.00                   ( ![E:$i]:
% 6.76/7.00                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 6.76/7.00                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 6.76/7.00                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.76/7.00  thf(zf_stmt_0, negated_conjecture,
% 6.76/7.00    (~( ![A:$i]:
% 6.76/7.00        ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.76/7.00          ( ![B:$i]:
% 6.76/7.00            ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.76/7.00              ( ![C:$i]:
% 6.76/7.00                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.76/7.00                    ( m1_subset_1 @
% 6.76/7.00                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.76/7.00                  ( ![D:$i]:
% 6.76/7.00                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 6.76/7.00                      ( ![E:$i]:
% 6.76/7.00                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 6.76/7.00                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 6.76/7.00                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 6.76/7.00    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 6.76/7.00  thf('0', plain,
% 6.76/7.00      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 6.76/7.00        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('1', plain,
% 6.76/7.00      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 6.76/7.00      inference('split', [status(esa)], ['0'])).
% 6.76/7.00  thf('2', plain,
% 6.76/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(redefinition_k7_relset_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i,D:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.76/7.00       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 6.76/7.00  thf('3', plain,
% 6.76/7.00      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 6.76/7.00         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 6.76/7.00          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 6.76/7.00      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.76/7.00  thf('4', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['2', '3'])).
% 6.76/7.00  thf('5', plain,
% 6.76/7.00      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 6.76/7.00      inference('demod', [status(thm)], ['1', '4'])).
% 6.76/7.00  thf('6', plain,
% 6.76/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(redefinition_k8_relset_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i,D:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.76/7.00       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 6.76/7.00  thf('7', plain,
% 6.76/7.00      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 6.76/7.00         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 6.76/7.00          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 6.76/7.00      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 6.76/7.00  thf('8', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['6', '7'])).
% 6.76/7.00  thf('9', plain,
% 6.76/7.00      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('split', [status(esa)], ['0'])).
% 6.76/7.00  thf('10', plain,
% 6.76/7.00      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('sup-', [status(thm)], ['8', '9'])).
% 6.76/7.00  thf('11', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 6.76/7.00        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('12', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['6', '7'])).
% 6.76/7.00  thf('13', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['2', '3'])).
% 6.76/7.00  thf('14', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 6.76/7.00        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))),
% 6.76/7.00      inference('demod', [status(thm)], ['11', '12', '13'])).
% 6.76/7.00  thf('15', plain,
% 6.76/7.00      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('sup-', [status(thm)], ['8', '9'])).
% 6.76/7.00  thf('16', plain,
% 6.76/7.00      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('sup-', [status(thm)], ['14', '15'])).
% 6.76/7.00  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(d1_funct_2, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.76/7.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.76/7.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.76/7.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.76/7.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.76/7.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.76/7.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.76/7.00  thf(zf_stmt_1, axiom,
% 6.76/7.00    (![C:$i,B:$i,A:$i]:
% 6.76/7.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.76/7.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.76/7.00  thf('18', plain,
% 6.76/7.00      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.76/7.00         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 6.76/7.00          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 6.76/7.00          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.76/7.00  thf('19', plain,
% 6.76/7.00      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.76/7.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 6.76/7.00      inference('sup-', [status(thm)], ['17', '18'])).
% 6.76/7.00  thf('20', plain,
% 6.76/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(redefinition_k1_relset_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.76/7.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.76/7.00  thf('21', plain,
% 6.76/7.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.76/7.00         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 6.76/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.76/7.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.76/7.00  thf('22', plain,
% 6.76/7.00      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.76/7.00      inference('sup-', [status(thm)], ['20', '21'])).
% 6.76/7.00  thf('23', plain,
% 6.76/7.00      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.76/7.00        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.76/7.00      inference('demod', [status(thm)], ['19', '22'])).
% 6.76/7.00  thf(zf_stmt_2, axiom,
% 6.76/7.00    (![B:$i,A:$i]:
% 6.76/7.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.76/7.00       ( zip_tseitin_0 @ B @ A ) ))).
% 6.76/7.00  thf('24', plain,
% 6.76/7.00      (![X35 : $i, X36 : $i]:
% 6.76/7.00         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.76/7.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.76/7.00  thf('25', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 6.76/7.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.76/7.00  thf('26', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.76/7.00         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 6.76/7.00      inference('sup+', [status(thm)], ['24', '25'])).
% 6.76/7.00  thf(existence_m1_subset_1, axiom,
% 6.76/7.00    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 6.76/7.00  thf('27', plain, (![X4 : $i]: (m1_subset_1 @ (sk_B @ X4) @ X4)),
% 6.76/7.00      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 6.76/7.00  thf(t2_subset, axiom,
% 6.76/7.00    (![A:$i,B:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ A @ B ) =>
% 6.76/7.00       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 6.76/7.00  thf('28', plain,
% 6.76/7.00      (![X5 : $i, X6 : $i]:
% 6.76/7.00         ((r2_hidden @ X5 @ X6)
% 6.76/7.00          | (v1_xboole_0 @ X6)
% 6.76/7.00          | ~ (m1_subset_1 @ X5 @ X6))),
% 6.76/7.00      inference('cnf', [status(esa)], [t2_subset])).
% 6.76/7.00  thf('29', plain,
% 6.76/7.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['27', '28'])).
% 6.76/7.00  thf(t7_ordinal1, axiom,
% 6.76/7.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.76/7.00  thf('30', plain,
% 6.76/7.00      (![X22 : $i, X23 : $i]:
% 6.76/7.00         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 6.76/7.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 6.76/7.00  thf('31', plain,
% 6.76/7.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 6.76/7.00      inference('sup-', [status(thm)], ['29', '30'])).
% 6.76/7.00  thf('32', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['26', '31'])).
% 6.76/7.00  thf('33', plain,
% 6.76/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.76/7.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.76/7.00  thf(zf_stmt_5, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.76/7.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.76/7.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.76/7.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.76/7.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.76/7.00  thf('34', plain,
% 6.76/7.00      (![X40 : $i, X41 : $i, X42 : $i]:
% 6.76/7.00         (~ (zip_tseitin_0 @ X40 @ X41)
% 6.76/7.00          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 6.76/7.00          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.76/7.00  thf('35', plain,
% 6.76/7.00      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.76/7.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.76/7.00      inference('sup-', [status(thm)], ['33', '34'])).
% 6.76/7.00  thf('36', plain,
% 6.76/7.00      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 6.76/7.00      inference('sup-', [status(thm)], ['32', '35'])).
% 6.76/7.00  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('38', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 6.76/7.00      inference('clc', [status(thm)], ['36', '37'])).
% 6.76/7.00  thf('39', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 6.76/7.00      inference('demod', [status(thm)], ['23', '38'])).
% 6.76/7.00  thf(t163_funct_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 6.76/7.00       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 6.76/7.00           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 6.76/7.00         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 6.76/7.00  thf('40', plain,
% 6.76/7.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.76/7.00         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 6.76/7.00          | ~ (r1_tarski @ (k9_relat_1 @ X20 @ X19) @ X21)
% 6.76/7.00          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ X21))
% 6.76/7.00          | ~ (v1_funct_1 @ X20)
% 6.76/7.00          | ~ (v1_relat_1 @ X20))),
% 6.76/7.00      inference('cnf', [status(esa)], [t163_funct_1])).
% 6.76/7.00  thf('41', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i]:
% 6.76/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.76/7.00          | ~ (v1_relat_1 @ sk_C)
% 6.76/7.00          | ~ (v1_funct_1 @ sk_C)
% 6.76/7.00          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 6.76/7.00          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 6.76/7.00      inference('sup-', [status(thm)], ['39', '40'])).
% 6.76/7.00  thf('42', plain,
% 6.76/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(cc2_relat_1, axiom,
% 6.76/7.00    (![A:$i]:
% 6.76/7.00     ( ( v1_relat_1 @ A ) =>
% 6.76/7.00       ( ![B:$i]:
% 6.76/7.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.76/7.00  thf('43', plain,
% 6.76/7.00      (![X10 : $i, X11 : $i]:
% 6.76/7.00         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.76/7.00          | (v1_relat_1 @ X10)
% 6.76/7.00          | ~ (v1_relat_1 @ X11))),
% 6.76/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.76/7.00  thf('44', plain,
% 6.76/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 6.76/7.00      inference('sup-', [status(thm)], ['42', '43'])).
% 6.76/7.00  thf(fc6_relat_1, axiom,
% 6.76/7.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.76/7.00  thf('45', plain,
% 6.76/7.00      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 6.76/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.76/7.00  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 6.76/7.00      inference('demod', [status(thm)], ['44', '45'])).
% 6.76/7.00  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('48', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i]:
% 6.76/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.76/7.00          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 6.76/7.00          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 6.76/7.00      inference('demod', [status(thm)], ['41', '46', '47'])).
% 6.76/7.00  thf('49', plain,
% 6.76/7.00      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 6.76/7.00         | ~ (r1_tarski @ sk_D @ sk_A)))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('sup-', [status(thm)], ['16', '48'])).
% 6.76/7.00  thf('50', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf(t3_subset, axiom,
% 6.76/7.00    (![A:$i,B:$i]:
% 6.76/7.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.76/7.00  thf('51', plain,
% 6.76/7.00      (![X7 : $i, X8 : $i]:
% 6.76/7.00         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 6.76/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.76/7.00  thf('52', plain, ((r1_tarski @ sk_D @ sk_A)),
% 6.76/7.00      inference('sup-', [status(thm)], ['50', '51'])).
% 6.76/7.00  thf('53', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (~
% 6.76/7.00             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('demod', [status(thm)], ['49', '52'])).
% 6.76/7.00  thf('54', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 6.76/7.00      inference('demod', [status(thm)], ['10', '53'])).
% 6.76/7.00  thf('55', plain,
% 6.76/7.00      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)) | 
% 6.76/7.00       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 6.76/7.00      inference('split', [status(esa)], ['0'])).
% 6.76/7.00  thf('56', plain,
% 6.76/7.00      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 6.76/7.00      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 6.76/7.00  thf('57', plain, (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 6.76/7.00      inference('simpl_trail', [status(thm)], ['5', '56'])).
% 6.76/7.00  thf(t145_funct_1, axiom,
% 6.76/7.00    (![A:$i,B:$i]:
% 6.76/7.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.76/7.00       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 6.76/7.00  thf('58', plain,
% 6.76/7.00      (![X17 : $i, X18 : $i]:
% 6.76/7.00         ((r1_tarski @ (k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X18)) @ X18)
% 6.76/7.00          | ~ (v1_funct_1 @ X17)
% 6.76/7.00          | ~ (v1_relat_1 @ X17))),
% 6.76/7.00      inference('cnf', [status(esa)], [t145_funct_1])).
% 6.76/7.00  thf('59', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 6.76/7.00        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('60', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('split', [status(esa)], ['59'])).
% 6.76/7.00  thf('61', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['6', '7'])).
% 6.76/7.00  thf('62', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 6.76/7.00         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 6.76/7.00      inference('demod', [status(thm)], ['60', '61'])).
% 6.76/7.00  thf('63', plain,
% 6.76/7.00      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 6.76/7.00      inference('sat_resolution*', [status(thm)], ['54'])).
% 6.76/7.00  thf('64', plain, ((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 6.76/7.00      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 6.76/7.00  thf(t156_relat_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( v1_relat_1 @ C ) =>
% 6.76/7.00       ( ( r1_tarski @ A @ B ) =>
% 6.76/7.00         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 6.76/7.00  thf('65', plain,
% 6.76/7.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.76/7.00         (~ (r1_tarski @ X14 @ X15)
% 6.76/7.00          | ~ (v1_relat_1 @ X16)
% 6.76/7.00          | (r1_tarski @ (k9_relat_1 @ X16 @ X14) @ (k9_relat_1 @ X16 @ X15)))),
% 6.76/7.00      inference('cnf', [status(esa)], [t156_relat_1])).
% 6.76/7.00  thf('66', plain,
% 6.76/7.00      (![X0 : $i]:
% 6.76/7.00         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 6.76/7.00           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 6.76/7.00          | ~ (v1_relat_1 @ X0))),
% 6.76/7.00      inference('sup-', [status(thm)], ['64', '65'])).
% 6.76/7.00  thf(t1_xboole_1, axiom,
% 6.76/7.00    (![A:$i,B:$i,C:$i]:
% 6.76/7.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.76/7.00       ( r1_tarski @ A @ C ) ))).
% 6.76/7.00  thf('67', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.76/7.00         (~ (r1_tarski @ X0 @ X1)
% 6.76/7.00          | ~ (r1_tarski @ X1 @ X2)
% 6.76/7.00          | (r1_tarski @ X0 @ X2))),
% 6.76/7.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.76/7.00  thf('68', plain,
% 6.76/7.00      (![X0 : $i, X1 : $i]:
% 6.76/7.00         (~ (v1_relat_1 @ X0)
% 6.76/7.00          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 6.76/7.00          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1))),
% 6.76/7.00      inference('sup-', [status(thm)], ['66', '67'])).
% 6.76/7.00  thf('69', plain,
% 6.76/7.00      ((~ (v1_relat_1 @ sk_C)
% 6.76/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.76/7.00        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 6.76/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.76/7.00      inference('sup-', [status(thm)], ['58', '68'])).
% 6.76/7.00  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 6.76/7.00      inference('demod', [status(thm)], ['44', '45'])).
% 6.76/7.00  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 6.76/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.76/7.00  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 6.76/7.00      inference('demod', [status(thm)], ['44', '45'])).
% 6.76/7.00  thf('73', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 6.76/7.00      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 6.76/7.00  thf('74', plain, ($false), inference('demod', [status(thm)], ['57', '73'])).
% 6.76/7.00  
% 6.76/7.00  % SZS output end Refutation
% 6.76/7.00  
% 6.84/7.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
