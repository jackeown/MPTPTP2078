%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YdLjzhfhHW

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 159 expanded)
%              Number of leaves         :   41 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  906 (2522 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','19','22'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X14 @ X13 ) @ X15 )
      | ( r1_tarski @ X13 @ ( k10_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ~ ( r1_tarski @ sk_D @ sk_A ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X10 @ X8 ) @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
          = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YdLjzhfhHW
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.87/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.08  % Solved by: fo/fo7.sh
% 0.87/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.08  % done 286 iterations in 0.621s
% 0.87/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.08  % SZS output start Refutation
% 0.87/1.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.87/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.87/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.87/1.08  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.87/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.08  thf(sk_E_type, type, sk_E: $i).
% 0.87/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.87/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.87/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.87/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.87/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.87/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.87/1.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.87/1.08  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.87/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.87/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.87/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.08  thf(t172_funct_2, conjecture,
% 0.87/1.08    (![A:$i]:
% 0.87/1.08     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.87/1.08       ( ![B:$i]:
% 0.87/1.08         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.87/1.08           ( ![C:$i]:
% 0.87/1.08             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.08                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.08               ( ![D:$i]:
% 0.87/1.08                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.08                   ( ![E:$i]:
% 0.87/1.08                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.87/1.08                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.87/1.08                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.87/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.08    (~( ![A:$i]:
% 0.87/1.08        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.87/1.08          ( ![B:$i]:
% 0.87/1.08            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.87/1.08              ( ![C:$i]:
% 0.87/1.08                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.08                    ( m1_subset_1 @
% 0.87/1.08                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.08                  ( ![D:$i]:
% 0.87/1.08                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.08                      ( ![E:$i]:
% 0.87/1.08                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.87/1.08                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.87/1.08                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.87/1.08    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.87/1.08  thf('0', plain,
% 0.87/1.08      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.87/1.08        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('1', plain,
% 0.87/1.08      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.87/1.08       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf('2', plain,
% 0.87/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(redefinition_k7_relset_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.87/1.08  thf('3', plain,
% 0.87/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.87/1.08         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.87/1.08          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.87/1.08      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.87/1.08  thf('4', plain,
% 0.87/1.08      (![X0 : $i]:
% 0.87/1.08         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.08  thf('5', plain,
% 0.87/1.08      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.87/1.08        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('6', plain,
% 0.87/1.08      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.87/1.08         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('split', [status(esa)], ['5'])).
% 0.87/1.08  thf('7', plain,
% 0.87/1.08      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.87/1.08         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('sup+', [status(thm)], ['4', '6'])).
% 0.87/1.08  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(d1_funct_2, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.87/1.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.87/1.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.87/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.87/1.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.87/1.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.87/1.08  thf(zf_stmt_1, axiom,
% 0.87/1.08    (![C:$i,B:$i,A:$i]:
% 0.87/1.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.87/1.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.87/1.08  thf('9', plain,
% 0.87/1.08      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.87/1.08         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.87/1.08          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.87/1.08          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.87/1.08  thf('10', plain,
% 0.87/1.08      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.87/1.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.87/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.87/1.08  thf(zf_stmt_2, axiom,
% 0.87/1.08    (![B:$i,A:$i]:
% 0.87/1.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.87/1.08       ( zip_tseitin_0 @ B @ A ) ))).
% 0.87/1.08  thf('11', plain,
% 0.87/1.08      (![X30 : $i, X31 : $i]:
% 0.87/1.08         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.87/1.08  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.08  thf('13', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.87/1.08      inference('sup+', [status(thm)], ['11', '12'])).
% 0.87/1.08  thf('14', plain,
% 0.87/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.87/1.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.87/1.08  thf(zf_stmt_5, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.87/1.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.87/1.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.87/1.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.87/1.08  thf('15', plain,
% 0.87/1.08      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.87/1.08         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.87/1.08          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.87/1.08          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.87/1.08  thf('16', plain,
% 0.87/1.08      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.87/1.08      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.08  thf('17', plain,
% 0.87/1.08      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.87/1.08      inference('sup-', [status(thm)], ['13', '16'])).
% 0.87/1.08  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('19', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.87/1.08      inference('clc', [status(thm)], ['17', '18'])).
% 0.87/1.08  thf('20', plain,
% 0.87/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(redefinition_k1_relset_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.87/1.08  thf('21', plain,
% 0.87/1.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.87/1.08         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.87/1.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.87/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.87/1.08  thf('22', plain,
% 0.87/1.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.87/1.08      inference('sup-', [status(thm)], ['20', '21'])).
% 0.87/1.08  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.87/1.08      inference('demod', [status(thm)], ['10', '19', '22'])).
% 0.87/1.08  thf(t163_funct_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.87/1.08       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.87/1.08           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.87/1.08         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.87/1.08  thf('24', plain,
% 0.87/1.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.87/1.08         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.87/1.08          | ~ (r1_tarski @ (k9_relat_1 @ X14 @ X13) @ X15)
% 0.87/1.08          | (r1_tarski @ X13 @ (k10_relat_1 @ X14 @ X15))
% 0.87/1.08          | ~ (v1_funct_1 @ X14)
% 0.87/1.08          | ~ (v1_relat_1 @ X14))),
% 0.87/1.08      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.87/1.08  thf('25', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         (~ (r1_tarski @ X0 @ sk_A)
% 0.87/1.08          | ~ (v1_relat_1 @ sk_C)
% 0.87/1.08          | ~ (v1_funct_1 @ sk_C)
% 0.87/1.08          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.87/1.08          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.87/1.08      inference('sup-', [status(thm)], ['23', '24'])).
% 0.87/1.08  thf('26', plain,
% 0.87/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(cc1_relset_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( v1_relat_1 @ C ) ))).
% 0.87/1.08  thf('27', plain,
% 0.87/1.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.87/1.08         ((v1_relat_1 @ X16)
% 0.87/1.08          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.87/1.08      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.87/1.08  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.87/1.08      inference('sup-', [status(thm)], ['26', '27'])).
% 0.87/1.08  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('30', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i]:
% 0.87/1.08         (~ (r1_tarski @ X0 @ sk_A)
% 0.87/1.08          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.87/1.08          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.87/1.08      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.87/1.08  thf('31', plain,
% 0.87/1.08      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 0.87/1.08         | ~ (r1_tarski @ sk_D @ sk_A)))
% 0.87/1.08         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('sup-', [status(thm)], ['7', '30'])).
% 0.87/1.08  thf('32', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(t3_subset, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.08  thf('33', plain,
% 0.87/1.08      (![X5 : $i, X6 : $i]:
% 0.87/1.08         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.87/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.08  thf('34', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.87/1.08      inference('sup-', [status(thm)], ['32', '33'])).
% 0.87/1.08  thf('35', plain,
% 0.87/1.08      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.87/1.08         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('demod', [status(thm)], ['31', '34'])).
% 0.87/1.08  thf('36', plain,
% 0.87/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf(redefinition_k8_relset_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.08       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.87/1.08  thf('37', plain,
% 0.87/1.08      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.87/1.08         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.87/1.08          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.87/1.08      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.87/1.08  thf('38', plain,
% 0.87/1.08      (![X0 : $i]:
% 0.87/1.08         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['36', '37'])).
% 0.87/1.08  thf('39', plain,
% 0.87/1.08      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.87/1.08         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf('40', plain,
% 0.87/1.08      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.87/1.08         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.87/1.08  thf('41', plain,
% 0.87/1.08      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.87/1.08       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('sup-', [status(thm)], ['35', '40'])).
% 0.87/1.08  thf('42', plain,
% 0.87/1.08      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.87/1.08       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('split', [status(esa)], ['5'])).
% 0.87/1.08  thf(t145_funct_1, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.87/1.08       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.87/1.08  thf('43', plain,
% 0.87/1.08      (![X11 : $i, X12 : $i]:
% 0.87/1.08         ((r1_tarski @ (k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X12)) @ X12)
% 0.87/1.08          | ~ (v1_funct_1 @ X11)
% 0.87/1.08          | ~ (v1_relat_1 @ X11))),
% 0.87/1.08      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.87/1.08  thf('44', plain,
% 0.87/1.08      (![X0 : $i]:
% 0.87/1.08         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['36', '37'])).
% 0.87/1.08  thf('45', plain,
% 0.87/1.08      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('split', [status(esa)], ['5'])).
% 0.87/1.08  thf(t156_relat_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( v1_relat_1 @ C ) =>
% 0.87/1.08       ( ( r1_tarski @ A @ B ) =>
% 0.87/1.08         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.87/1.08  thf('46', plain,
% 0.87/1.08      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.87/1.08         (~ (r1_tarski @ X8 @ X9)
% 0.87/1.08          | ~ (v1_relat_1 @ X10)
% 0.87/1.08          | (r1_tarski @ (k9_relat_1 @ X10 @ X8) @ (k9_relat_1 @ X10 @ X9)))),
% 0.87/1.08      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.87/1.08  thf('47', plain,
% 0.87/1.08      ((![X0 : $i]:
% 0.87/1.08          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.87/1.08            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.87/1.08           | ~ (v1_relat_1 @ X0)))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['45', '46'])).
% 0.87/1.08  thf('48', plain,
% 0.87/1.08      ((![X0 : $i]:
% 0.87/1.08          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.87/1.08            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.87/1.08           | ~ (v1_relat_1 @ X0)))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup+', [status(thm)], ['44', '47'])).
% 0.87/1.08  thf(t12_xboole_1, axiom,
% 0.87/1.08    (![A:$i,B:$i]:
% 0.87/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.87/1.08  thf('49', plain,
% 0.87/1.08      (![X3 : $i, X4 : $i]:
% 0.87/1.08         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.87/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.87/1.08  thf('50', plain,
% 0.87/1.08      ((![X0 : $i]:
% 0.87/1.08          (~ (v1_relat_1 @ X0)
% 0.87/1.08           | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.87/1.08               (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.87/1.08               = (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['48', '49'])).
% 0.87/1.08  thf(t11_xboole_1, axiom,
% 0.87/1.08    (![A:$i,B:$i,C:$i]:
% 0.87/1.08     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.87/1.08  thf('51', plain,
% 0.87/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.08         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.87/1.08      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.87/1.08  thf('52', plain,
% 0.87/1.08      ((![X0 : $i, X1 : $i]:
% 0.87/1.08          (~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1)
% 0.87/1.08           | ~ (v1_relat_1 @ X0)
% 0.87/1.08           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['50', '51'])).
% 0.87/1.08  thf('53', plain,
% 0.87/1.08      (((~ (v1_relat_1 @ sk_C)
% 0.87/1.08         | ~ (v1_funct_1 @ sk_C)
% 0.87/1.08         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 0.87/1.08         | ~ (v1_relat_1 @ sk_C)))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('sup-', [status(thm)], ['43', '52'])).
% 0.87/1.08  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.87/1.08      inference('sup-', [status(thm)], ['26', '27'])).
% 0.87/1.08  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.87/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.08  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.87/1.08      inference('sup-', [status(thm)], ['26', '27'])).
% 0.87/1.08  thf('57', plain,
% 0.87/1.08      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.87/1.08         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.87/1.08      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.87/1.08  thf('58', plain,
% 0.87/1.08      (![X0 : $i]:
% 0.87/1.08         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.87/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.08  thf('59', plain,
% 0.87/1.08      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.87/1.08         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('split', [status(esa)], ['0'])).
% 0.87/1.08  thf('60', plain,
% 0.87/1.08      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.87/1.08         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.87/1.08      inference('sup-', [status(thm)], ['58', '59'])).
% 0.87/1.08  thf('61', plain,
% 0.87/1.08      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.87/1.08       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.87/1.08      inference('sup-', [status(thm)], ['57', '60'])).
% 0.87/1.08  thf('62', plain, ($false),
% 0.87/1.08      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '61'])).
% 0.87/1.08  
% 0.87/1.08  % SZS output end Refutation
% 0.87/1.08  
% 0.93/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
