%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DaRMbHigdc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 283 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  915 (4507 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X16 @ X15 ) @ X17 )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','44','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ~ ( r1_tarski @ sk_D @ sk_A ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['10','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['5','54'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('57',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['52'])).

thf('62',plain,(
    r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X12 @ X10 ) @ ( k9_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('71',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['55','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DaRMbHigdc
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.45/2.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.45/2.67  % Solved by: fo/fo7.sh
% 2.45/2.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.45/2.67  % done 2189 iterations in 2.222s
% 2.45/2.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.45/2.67  % SZS output start Refutation
% 2.45/2.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.45/2.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.45/2.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.45/2.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.45/2.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.45/2.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.45/2.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.45/2.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.45/2.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.45/2.67  thf(sk_C_type, type, sk_C: $i).
% 2.45/2.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.45/2.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.45/2.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.45/2.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.45/2.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.45/2.67  thf(sk_D_type, type, sk_D: $i).
% 2.45/2.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.45/2.67  thf(sk_E_type, type, sk_E: $i).
% 2.45/2.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.45/2.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.45/2.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.45/2.67  thf(sk_B_type, type, sk_B: $i > $i).
% 2.45/2.67  thf(sk_A_type, type, sk_A: $i).
% 2.45/2.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.45/2.67  thf(t172_funct_2, conjecture,
% 2.45/2.67    (![A:$i]:
% 2.45/2.67     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.45/2.67       ( ![B:$i]:
% 2.45/2.67         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.45/2.67           ( ![C:$i]:
% 2.45/2.67             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.45/2.67                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.45/2.67               ( ![D:$i]:
% 2.45/2.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 2.45/2.67                   ( ![E:$i]:
% 2.45/2.67                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 2.45/2.67                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 2.45/2.67                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.45/2.67  thf(zf_stmt_0, negated_conjecture,
% 2.45/2.67    (~( ![A:$i]:
% 2.45/2.67        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.45/2.67          ( ![B:$i]:
% 2.45/2.67            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.45/2.67              ( ![C:$i]:
% 2.45/2.67                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.45/2.67                    ( m1_subset_1 @
% 2.45/2.67                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.45/2.67                  ( ![D:$i]:
% 2.45/2.67                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 2.45/2.67                      ( ![E:$i]:
% 2.45/2.67                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 2.45/2.67                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 2.45/2.67                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.45/2.67    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 2.45/2.67  thf('0', plain,
% 2.45/2.67      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 2.45/2.67        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('1', plain,
% 2.45/2.67      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 2.45/2.67      inference('split', [status(esa)], ['0'])).
% 2.45/2.67  thf('2', plain,
% 2.45/2.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(redefinition_k7_relset_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i,D:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 2.45/2.67  thf('3', plain,
% 2.45/2.67      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.45/2.67         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.45/2.67          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 2.45/2.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 2.45/2.67  thf('4', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['2', '3'])).
% 2.45/2.67  thf('5', plain,
% 2.45/2.67      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 2.45/2.67      inference('demod', [status(thm)], ['1', '4'])).
% 2.45/2.67  thf('6', plain,
% 2.45/2.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(redefinition_k8_relset_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i,D:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.45/2.67  thf('7', plain,
% 2.45/2.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.45/2.67         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.45/2.67          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 2.45/2.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.45/2.67  thf('8', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['6', '7'])).
% 2.45/2.67  thf('9', plain,
% 2.45/2.67      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('split', [status(esa)], ['0'])).
% 2.45/2.67  thf('10', plain,
% 2.45/2.67      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('sup-', [status(thm)], ['8', '9'])).
% 2.45/2.67  thf('11', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 2.45/2.67        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('12', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['6', '7'])).
% 2.45/2.67  thf('13', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['2', '3'])).
% 2.45/2.67  thf('14', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 2.45/2.67        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))),
% 2.45/2.67      inference('demod', [status(thm)], ['11', '12', '13'])).
% 2.45/2.67  thf('15', plain,
% 2.45/2.67      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('sup-', [status(thm)], ['8', '9'])).
% 2.45/2.67  thf('16', plain,
% 2.45/2.67      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('sup-', [status(thm)], ['14', '15'])).
% 2.45/2.67  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(d1_funct_2, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.45/2.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.45/2.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.45/2.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.45/2.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.45/2.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.45/2.67  thf(zf_stmt_1, axiom,
% 2.45/2.67    (![C:$i,B:$i,A:$i]:
% 2.45/2.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.45/2.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.45/2.67  thf('18', plain,
% 2.45/2.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.45/2.67         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 2.45/2.67          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 2.45/2.67          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.45/2.67  thf('19', plain,
% 2.45/2.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.45/2.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 2.45/2.67      inference('sup-', [status(thm)], ['17', '18'])).
% 2.45/2.67  thf('20', plain,
% 2.45/2.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(redefinition_k1_relset_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.45/2.67  thf('21', plain,
% 2.45/2.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.45/2.67         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 2.45/2.67          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.45/2.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.45/2.67  thf('22', plain,
% 2.45/2.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.45/2.67      inference('sup-', [status(thm)], ['20', '21'])).
% 2.45/2.67  thf('23', plain,
% 2.45/2.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.45/2.67        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.45/2.67      inference('demod', [status(thm)], ['19', '22'])).
% 2.45/2.67  thf(zf_stmt_2, axiom,
% 2.45/2.67    (![B:$i,A:$i]:
% 2.45/2.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.45/2.67       ( zip_tseitin_0 @ B @ A ) ))).
% 2.45/2.67  thf('24', plain,
% 2.45/2.67      (![X34 : $i, X35 : $i]:
% 2.45/2.67         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.45/2.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.45/2.67  thf('25', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.45/2.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.45/2.67  thf('26', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.67         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.45/2.67      inference('sup+', [status(thm)], ['24', '25'])).
% 2.45/2.67  thf(existence_m1_subset_1, axiom,
% 2.45/2.67    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 2.45/2.67  thf('27', plain, (![X4 : $i]: (m1_subset_1 @ (sk_B @ X4) @ X4)),
% 2.45/2.67      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 2.45/2.67  thf(t2_subset, axiom,
% 2.45/2.67    (![A:$i,B:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ A @ B ) =>
% 2.45/2.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.45/2.67  thf('28', plain,
% 2.45/2.67      (![X5 : $i, X6 : $i]:
% 2.45/2.67         ((r2_hidden @ X5 @ X6)
% 2.45/2.67          | (v1_xboole_0 @ X6)
% 2.45/2.67          | ~ (m1_subset_1 @ X5 @ X6))),
% 2.45/2.67      inference('cnf', [status(esa)], [t2_subset])).
% 2.45/2.67  thf('29', plain,
% 2.45/2.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['27', '28'])).
% 2.45/2.67  thf(t7_ordinal1, axiom,
% 2.45/2.67    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.45/2.67  thf('30', plain,
% 2.45/2.67      (![X18 : $i, X19 : $i]:
% 2.45/2.67         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 2.45/2.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.45/2.67  thf('31', plain,
% 2.45/2.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.45/2.67      inference('sup-', [status(thm)], ['29', '30'])).
% 2.45/2.67  thf('32', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['26', '31'])).
% 2.45/2.67  thf('33', plain,
% 2.45/2.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.45/2.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.45/2.67  thf(zf_stmt_5, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.45/2.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.45/2.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.45/2.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.45/2.67  thf('34', plain,
% 2.45/2.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.45/2.67         (~ (zip_tseitin_0 @ X39 @ X40)
% 2.45/2.67          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 2.45/2.67          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.45/2.67  thf('35', plain,
% 2.45/2.67      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 2.45/2.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.45/2.67      inference('sup-', [status(thm)], ['33', '34'])).
% 2.45/2.67  thf('36', plain,
% 2.45/2.67      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 2.45/2.67      inference('sup-', [status(thm)], ['32', '35'])).
% 2.45/2.67  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('38', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 2.45/2.67      inference('clc', [status(thm)], ['36', '37'])).
% 2.45/2.67  thf('39', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.45/2.67      inference('demod', [status(thm)], ['23', '38'])).
% 2.45/2.67  thf(t163_funct_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.45/2.67       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 2.45/2.67           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 2.45/2.67         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.45/2.67  thf('40', plain,
% 2.45/2.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.45/2.67         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 2.45/2.67          | ~ (r1_tarski @ (k9_relat_1 @ X16 @ X15) @ X17)
% 2.45/2.67          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ X17))
% 2.45/2.67          | ~ (v1_funct_1 @ X16)
% 2.45/2.67          | ~ (v1_relat_1 @ X16))),
% 2.45/2.67      inference('cnf', [status(esa)], [t163_funct_1])).
% 2.45/2.67  thf('41', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i]:
% 2.45/2.67         (~ (r1_tarski @ X0 @ sk_A)
% 2.45/2.67          | ~ (v1_relat_1 @ sk_C)
% 2.45/2.67          | ~ (v1_funct_1 @ sk_C)
% 2.45/2.67          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 2.45/2.67          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 2.45/2.67      inference('sup-', [status(thm)], ['39', '40'])).
% 2.45/2.67  thf('42', plain,
% 2.45/2.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(cc1_relset_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.45/2.67       ( v1_relat_1 @ C ) ))).
% 2.45/2.67  thf('43', plain,
% 2.45/2.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.45/2.67         ((v1_relat_1 @ X20)
% 2.45/2.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.45/2.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.45/2.67  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 2.45/2.67      inference('sup-', [status(thm)], ['42', '43'])).
% 2.45/2.67  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('46', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i]:
% 2.45/2.67         (~ (r1_tarski @ X0 @ sk_A)
% 2.45/2.67          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 2.45/2.67          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 2.45/2.67      inference('demod', [status(thm)], ['41', '44', '45'])).
% 2.45/2.67  thf('47', plain,
% 2.45/2.67      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 2.45/2.67         | ~ (r1_tarski @ sk_D @ sk_A)))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('sup-', [status(thm)], ['16', '46'])).
% 2.45/2.67  thf('48', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf(t3_subset, axiom,
% 2.45/2.67    (![A:$i,B:$i]:
% 2.45/2.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.45/2.67  thf('49', plain,
% 2.45/2.67      (![X7 : $i, X8 : $i]:
% 2.45/2.67         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.45/2.67      inference('cnf', [status(esa)], [t3_subset])).
% 2.45/2.67  thf('50', plain, ((r1_tarski @ sk_D @ sk_A)),
% 2.45/2.67      inference('sup-', [status(thm)], ['48', '49'])).
% 2.45/2.67  thf('51', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (~
% 2.45/2.67             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('demod', [status(thm)], ['47', '50'])).
% 2.45/2.67  thf('52', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 2.45/2.67      inference('demod', [status(thm)], ['10', '51'])).
% 2.45/2.67  thf('53', plain,
% 2.45/2.67      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)) | 
% 2.45/2.67       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 2.45/2.67      inference('split', [status(esa)], ['0'])).
% 2.45/2.67  thf('54', plain,
% 2.45/2.67      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 2.45/2.67      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 2.45/2.67  thf('55', plain, (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 2.45/2.67      inference('simpl_trail', [status(thm)], ['5', '54'])).
% 2.45/2.67  thf(t145_funct_1, axiom,
% 2.45/2.67    (![A:$i,B:$i]:
% 2.45/2.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.45/2.67       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.45/2.67  thf('56', plain,
% 2.45/2.67      (![X13 : $i, X14 : $i]:
% 2.45/2.67         ((r1_tarski @ (k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X14)) @ X14)
% 2.45/2.67          | ~ (v1_funct_1 @ X13)
% 2.45/2.67          | ~ (v1_relat_1 @ X13))),
% 2.45/2.67      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.45/2.67  thf('57', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 2.45/2.67        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('58', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('split', [status(esa)], ['57'])).
% 2.45/2.67  thf('59', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['6', '7'])).
% 2.45/2.67  thf('60', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 2.45/2.67         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 2.45/2.67      inference('demod', [status(thm)], ['58', '59'])).
% 2.45/2.67  thf('61', plain,
% 2.45/2.67      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 2.45/2.67      inference('sat_resolution*', [status(thm)], ['52'])).
% 2.45/2.67  thf('62', plain, ((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 2.45/2.67      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 2.45/2.67  thf(t156_relat_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( v1_relat_1 @ C ) =>
% 2.45/2.67       ( ( r1_tarski @ A @ B ) =>
% 2.45/2.67         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 2.45/2.67  thf('63', plain,
% 2.45/2.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.45/2.67         (~ (r1_tarski @ X10 @ X11)
% 2.45/2.67          | ~ (v1_relat_1 @ X12)
% 2.45/2.67          | (r1_tarski @ (k9_relat_1 @ X12 @ X10) @ (k9_relat_1 @ X12 @ X11)))),
% 2.45/2.67      inference('cnf', [status(esa)], [t156_relat_1])).
% 2.45/2.67  thf('64', plain,
% 2.45/2.67      (![X0 : $i]:
% 2.45/2.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 2.45/2.67           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 2.45/2.67          | ~ (v1_relat_1 @ X0))),
% 2.45/2.67      inference('sup-', [status(thm)], ['62', '63'])).
% 2.45/2.67  thf(t1_xboole_1, axiom,
% 2.45/2.67    (![A:$i,B:$i,C:$i]:
% 2.45/2.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.45/2.67       ( r1_tarski @ A @ C ) ))).
% 2.45/2.67  thf('65', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.67         (~ (r1_tarski @ X0 @ X1)
% 2.45/2.67          | ~ (r1_tarski @ X1 @ X2)
% 2.45/2.67          | (r1_tarski @ X0 @ X2))),
% 2.45/2.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.45/2.67  thf('66', plain,
% 2.45/2.67      (![X0 : $i, X1 : $i]:
% 2.45/2.67         (~ (v1_relat_1 @ X0)
% 2.45/2.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 2.45/2.67          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1))),
% 2.45/2.67      inference('sup-', [status(thm)], ['64', '65'])).
% 2.45/2.67  thf('67', plain,
% 2.45/2.67      ((~ (v1_relat_1 @ sk_C)
% 2.45/2.67        | ~ (v1_funct_1 @ sk_C)
% 2.45/2.67        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 2.45/2.67        | ~ (v1_relat_1 @ sk_C))),
% 2.45/2.67      inference('sup-', [status(thm)], ['56', '66'])).
% 2.45/2.67  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 2.45/2.67      inference('sup-', [status(thm)], ['42', '43'])).
% 2.45/2.67  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 2.45/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.67  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 2.45/2.67      inference('sup-', [status(thm)], ['42', '43'])).
% 2.45/2.67  thf('71', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 2.45/2.67      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 2.45/2.67  thf('72', plain, ($false), inference('demod', [status(thm)], ['55', '71'])).
% 2.45/2.67  
% 2.45/2.67  % SZS output end Refutation
% 2.45/2.67  
% 2.45/2.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
