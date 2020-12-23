%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d4dc3CYJor

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:35 EST 2020

% Result     : Theorem 5.50s
% Output     : Refutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 320 expanded)
%              Number of leaves         :   40 ( 109 expanded)
%              Depth                    :   19
%              Number of atoms          :  919 (5005 expanded)
%              Number of equality atoms :   29 (  74 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k7_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k9_relat_1 @ X42 @ X45 ) ) ) ),
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

thf('6',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k8_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k10_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X55 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X55 ) ) )
      | ( ( k8_relset_1 @ X53 @ X55 @ X54 @ X55 )
        = X53 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('18',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1 )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B_1 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k1_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X35 @ X34 ) @ X36 )
      | ( r1_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('50',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['5','58'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('60',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X33 ) ) @ X33 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('61',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['61'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k9_relat_1 @ X29 @ X27 ) @ ( k9_relat_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['56'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('75',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['59','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d4dc3CYJor
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.50/5.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.50/5.71  % Solved by: fo/fo7.sh
% 5.50/5.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.50/5.71  % done 9069 iterations in 5.264s
% 5.50/5.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.50/5.71  % SZS output start Refutation
% 5.50/5.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.50/5.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.50/5.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.50/5.71  thf(sk_A_type, type, sk_A: $i).
% 5.50/5.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.50/5.71  thf(sk_E_type, type, sk_E: $i).
% 5.50/5.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.50/5.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.50/5.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.50/5.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.50/5.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.50/5.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.50/5.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.50/5.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.50/5.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.50/5.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 5.50/5.71  thf(sk_B_type, type, sk_B: $i > $i).
% 5.50/5.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.50/5.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 5.50/5.71  thf(sk_C_type, type, sk_C: $i).
% 5.50/5.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.50/5.71  thf(sk_D_type, type, sk_D: $i).
% 5.50/5.71  thf(t172_funct_2, conjecture,
% 5.50/5.71    (![A:$i]:
% 5.50/5.71     ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.50/5.71       ( ![B:$i]:
% 5.50/5.71         ( ( ~( v1_xboole_0 @ B ) ) =>
% 5.50/5.71           ( ![C:$i]:
% 5.50/5.71             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.50/5.71                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.50/5.71               ( ![D:$i]:
% 5.50/5.71                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 5.50/5.71                   ( ![E:$i]:
% 5.50/5.71                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 5.50/5.71                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 5.50/5.71                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.50/5.71  thf(zf_stmt_0, negated_conjecture,
% 5.50/5.71    (~( ![A:$i]:
% 5.50/5.71        ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.50/5.71          ( ![B:$i]:
% 5.50/5.71            ( ( ~( v1_xboole_0 @ B ) ) =>
% 5.50/5.71              ( ![C:$i]:
% 5.50/5.71                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.50/5.71                    ( m1_subset_1 @
% 5.50/5.71                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.50/5.71                  ( ![D:$i]:
% 5.50/5.71                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 5.50/5.71                      ( ![E:$i]:
% 5.50/5.71                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 5.50/5.71                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 5.50/5.71                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 5.50/5.71    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 5.50/5.71  thf('0', plain,
% 5.50/5.71      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 5.50/5.71        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('1', plain,
% 5.50/5.71      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 5.50/5.71      inference('split', [status(esa)], ['0'])).
% 5.50/5.71  thf('2', plain,
% 5.50/5.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf(redefinition_k7_relset_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i,D:$i]:
% 5.50/5.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.50/5.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 5.50/5.71  thf('3', plain,
% 5.50/5.71      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 5.50/5.71         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 5.50/5.71          | ((k7_relset_1 @ X43 @ X44 @ X42 @ X45) = (k9_relat_1 @ X42 @ X45)))),
% 5.50/5.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 5.50/5.71  thf('4', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['2', '3'])).
% 5.50/5.71  thf('5', plain,
% 5.50/5.71      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 5.50/5.71      inference('demod', [status(thm)], ['1', '4'])).
% 5.50/5.71  thf('6', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 5.50/5.71        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('7', plain,
% 5.50/5.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf(redefinition_k8_relset_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i,D:$i]:
% 5.50/5.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.50/5.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 5.50/5.71  thf('8', plain,
% 5.50/5.71      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.50/5.71         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 5.50/5.71          | ((k8_relset_1 @ X47 @ X48 @ X46 @ X49) = (k10_relat_1 @ X46 @ X49)))),
% 5.50/5.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 5.50/5.71  thf('9', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['7', '8'])).
% 5.50/5.71  thf('10', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['2', '3'])).
% 5.50/5.71  thf('11', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 5.50/5.71        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))),
% 5.50/5.71      inference('demod', [status(thm)], ['6', '9', '10'])).
% 5.50/5.71  thf('12', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['7', '8'])).
% 5.50/5.71  thf('13', plain,
% 5.50/5.71      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('split', [status(esa)], ['0'])).
% 5.50/5.71  thf('14', plain,
% 5.50/5.71      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.50/5.71  thf('15', plain,
% 5.50/5.71      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['11', '14'])).
% 5.50/5.71  thf('16', plain,
% 5.50/5.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf(t48_funct_2, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i]:
% 5.50/5.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.50/5.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.50/5.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.50/5.71         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 5.50/5.71  thf('17', plain,
% 5.50/5.71      (![X53 : $i, X54 : $i, X55 : $i]:
% 5.50/5.71         (((X55) = (k1_xboole_0))
% 5.50/5.71          | ~ (v1_funct_1 @ X54)
% 5.50/5.71          | ~ (v1_funct_2 @ X54 @ X53 @ X55)
% 5.50/5.71          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X55)))
% 5.50/5.71          | ((k8_relset_1 @ X53 @ X55 @ X54 @ X55) = (X53)))),
% 5.50/5.71      inference('cnf', [status(esa)], [t48_funct_2])).
% 5.50/5.71  thf('18', plain,
% 5.50/5.71      ((((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1) = (sk_A))
% 5.50/5.71        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 5.50/5.71        | ~ (v1_funct_1 @ sk_C)
% 5.50/5.71        | ((sk_B_1) = (k1_xboole_0)))),
% 5.50/5.71      inference('sup-', [status(thm)], ['16', '17'])).
% 5.50/5.71  thf('19', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['7', '8'])).
% 5.50/5.71  thf('20', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('22', plain,
% 5.50/5.71      ((((k10_relat_1 @ sk_C @ sk_B_1) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 5.50/5.71      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 5.50/5.71  thf(t167_relat_1, axiom,
% 5.50/5.71    (![A:$i,B:$i]:
% 5.50/5.71     ( ( v1_relat_1 @ B ) =>
% 5.50/5.71       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 5.50/5.71  thf('23', plain,
% 5.50/5.71      (![X30 : $i, X31 : $i]:
% 5.50/5.71         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 5.50/5.71          | ~ (v1_relat_1 @ X30))),
% 5.50/5.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.50/5.71  thf('24', plain,
% 5.50/5.71      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 5.50/5.71        | ((sk_B_1) = (k1_xboole_0))
% 5.50/5.71        | ~ (v1_relat_1 @ sk_C))),
% 5.50/5.71      inference('sup+', [status(thm)], ['22', '23'])).
% 5.50/5.71  thf('25', plain,
% 5.50/5.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf(cc2_relat_1, axiom,
% 5.50/5.71    (![A:$i]:
% 5.50/5.71     ( ( v1_relat_1 @ A ) =>
% 5.50/5.71       ( ![B:$i]:
% 5.50/5.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.50/5.71  thf('26', plain,
% 5.50/5.71      (![X21 : $i, X22 : $i]:
% 5.50/5.71         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 5.50/5.71          | (v1_relat_1 @ X21)
% 5.50/5.71          | ~ (v1_relat_1 @ X22))),
% 5.50/5.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.50/5.71  thf('27', plain,
% 5.50/5.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 5.50/5.71      inference('sup-', [status(thm)], ['25', '26'])).
% 5.50/5.71  thf(fc6_relat_1, axiom,
% 5.50/5.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.50/5.71  thf('28', plain,
% 5.50/5.71      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 5.50/5.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.50/5.71  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 5.50/5.71      inference('demod', [status(thm)], ['27', '28'])).
% 5.50/5.71  thf('30', plain,
% 5.50/5.71      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 5.50/5.71      inference('demod', [status(thm)], ['24', '29'])).
% 5.50/5.71  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf(t3_subset, axiom,
% 5.50/5.71    (![A:$i,B:$i]:
% 5.50/5.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.50/5.71  thf('32', plain,
% 5.50/5.71      (![X18 : $i, X19 : $i]:
% 5.50/5.71         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 5.50/5.71      inference('cnf', [status(esa)], [t3_subset])).
% 5.50/5.71  thf('33', plain, ((r1_tarski @ sk_D @ sk_A)),
% 5.50/5.71      inference('sup-', [status(thm)], ['31', '32'])).
% 5.50/5.71  thf(t12_xboole_1, axiom,
% 5.50/5.71    (![A:$i,B:$i]:
% 5.50/5.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.50/5.71  thf('34', plain,
% 5.50/5.71      (![X3 : $i, X4 : $i]:
% 5.50/5.71         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 5.50/5.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.50/5.71  thf('35', plain, (((k2_xboole_0 @ sk_D @ sk_A) = (sk_A))),
% 5.50/5.71      inference('sup-', [status(thm)], ['33', '34'])).
% 5.50/5.71  thf(t11_xboole_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i]:
% 5.50/5.71     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.50/5.71  thf('36', plain,
% 5.50/5.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.50/5.71         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 5.50/5.71      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.50/5.71  thf('37', plain,
% 5.50/5.71      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_D @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['35', '36'])).
% 5.50/5.71  thf('38', plain,
% 5.50/5.71      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 5.50/5.71      inference('sup-', [status(thm)], ['30', '37'])).
% 5.50/5.71  thf(t163_funct_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i]:
% 5.50/5.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.50/5.71       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 5.50/5.71           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 5.50/5.71         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.50/5.71  thf('39', plain,
% 5.50/5.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 5.50/5.71         (~ (r1_tarski @ X34 @ (k1_relat_1 @ X35))
% 5.50/5.71          | ~ (r1_tarski @ (k9_relat_1 @ X35 @ X34) @ X36)
% 5.50/5.71          | (r1_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))
% 5.50/5.71          | ~ (v1_funct_1 @ X35)
% 5.50/5.71          | ~ (v1_relat_1 @ X35))),
% 5.50/5.71      inference('cnf', [status(esa)], [t163_funct_1])).
% 5.50/5.71  thf('40', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         (((sk_B_1) = (k1_xboole_0))
% 5.50/5.71          | ~ (v1_relat_1 @ sk_C)
% 5.50/5.71          | ~ (v1_funct_1 @ sk_C)
% 5.50/5.71          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 5.50/5.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['38', '39'])).
% 5.50/5.71  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 5.50/5.71      inference('demod', [status(thm)], ['27', '28'])).
% 5.50/5.71  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('43', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         (((sk_B_1) = (k1_xboole_0))
% 5.50/5.71          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 5.50/5.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 5.50/5.71      inference('demod', [status(thm)], ['40', '41', '42'])).
% 5.50/5.71  thf('44', plain,
% 5.50/5.71      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 5.50/5.71         | ((sk_B_1) = (k1_xboole_0))))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['15', '43'])).
% 5.50/5.71  thf('45', plain,
% 5.50/5.71      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.50/5.71  thf('46', plain,
% 5.50/5.71      ((((sk_B_1) = (k1_xboole_0)))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('clc', [status(thm)], ['44', '45'])).
% 5.50/5.71  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('48', plain,
% 5.50/5.71      ((~ (v1_xboole_0 @ k1_xboole_0))
% 5.50/5.71         <= (~
% 5.50/5.71             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['46', '47'])).
% 5.50/5.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.50/5.71  thf('49', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 5.50/5.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.50/5.71  thf(existence_m1_subset_1, axiom,
% 5.50/5.71    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 5.50/5.71  thf('50', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B @ X12) @ X12)),
% 5.50/5.71      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 5.50/5.71  thf(t2_subset, axiom,
% 5.50/5.71    (![A:$i,B:$i]:
% 5.50/5.71     ( ( m1_subset_1 @ A @ B ) =>
% 5.50/5.71       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 5.50/5.71  thf('51', plain,
% 5.50/5.71      (![X16 : $i, X17 : $i]:
% 5.50/5.71         ((r2_hidden @ X16 @ X17)
% 5.50/5.71          | (v1_xboole_0 @ X17)
% 5.50/5.71          | ~ (m1_subset_1 @ X16 @ X17))),
% 5.50/5.71      inference('cnf', [status(esa)], [t2_subset])).
% 5.50/5.71  thf('52', plain,
% 5.50/5.71      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['50', '51'])).
% 5.50/5.71  thf(t7_ordinal1, axiom,
% 5.50/5.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.50/5.71  thf('53', plain,
% 5.50/5.71      (![X37 : $i, X38 : $i]:
% 5.50/5.71         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 5.50/5.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.50/5.71  thf('54', plain,
% 5.50/5.71      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 5.50/5.71      inference('sup-', [status(thm)], ['52', '53'])).
% 5.50/5.71  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.50/5.71      inference('sup-', [status(thm)], ['49', '54'])).
% 5.50/5.71  thf('56', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 5.50/5.71      inference('demod', [status(thm)], ['48', '55'])).
% 5.50/5.71  thf('57', plain,
% 5.50/5.71      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)) | 
% 5.50/5.71       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 5.50/5.71      inference('split', [status(esa)], ['0'])).
% 5.50/5.71  thf('58', plain,
% 5.50/5.71      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 5.50/5.71      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 5.50/5.71  thf('59', plain, (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 5.50/5.71      inference('simpl_trail', [status(thm)], ['5', '58'])).
% 5.50/5.71  thf(t145_funct_1, axiom,
% 5.50/5.71    (![A:$i,B:$i]:
% 5.50/5.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.50/5.71       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 5.50/5.71  thf('60', plain,
% 5.50/5.71      (![X32 : $i, X33 : $i]:
% 5.50/5.71         ((r1_tarski @ (k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X33)) @ X33)
% 5.50/5.71          | ~ (v1_funct_1 @ X32)
% 5.50/5.71          | ~ (v1_relat_1 @ X32))),
% 5.50/5.71      inference('cnf', [status(esa)], [t145_funct_1])).
% 5.50/5.71  thf('61', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 5.50/5.71        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('62', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 5.50/5.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('split', [status(esa)], ['61'])).
% 5.50/5.71  thf(t156_relat_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i]:
% 5.50/5.71     ( ( v1_relat_1 @ C ) =>
% 5.50/5.71       ( ( r1_tarski @ A @ B ) =>
% 5.50/5.71         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 5.50/5.71  thf('63', plain,
% 5.50/5.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.50/5.71         (~ (r1_tarski @ X27 @ X28)
% 5.50/5.71          | ~ (v1_relat_1 @ X29)
% 5.50/5.71          | (r1_tarski @ (k9_relat_1 @ X29 @ X27) @ (k9_relat_1 @ X29 @ X28)))),
% 5.50/5.71      inference('cnf', [status(esa)], [t156_relat_1])).
% 5.50/5.71  thf('64', plain,
% 5.50/5.71      ((![X0 : $i]:
% 5.50/5.71          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 5.50/5.71            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 5.50/5.71           | ~ (v1_relat_1 @ X0)))
% 5.50/5.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('sup-', [status(thm)], ['62', '63'])).
% 5.50/5.71  thf('65', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 5.50/5.71      inference('sup-', [status(thm)], ['7', '8'])).
% 5.50/5.71  thf('66', plain,
% 5.50/5.71      ((![X0 : $i]:
% 5.50/5.71          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 5.50/5.71            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 5.50/5.71           | ~ (v1_relat_1 @ X0)))
% 5.50/5.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 5.50/5.71      inference('demod', [status(thm)], ['64', '65'])).
% 5.50/5.71  thf('67', plain,
% 5.50/5.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 5.50/5.71      inference('sat_resolution*', [status(thm)], ['56'])).
% 5.50/5.71  thf('68', plain,
% 5.50/5.71      (![X0 : $i]:
% 5.50/5.71         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 5.50/5.71           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 5.50/5.71          | ~ (v1_relat_1 @ X0))),
% 5.50/5.71      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 5.50/5.71  thf(t1_xboole_1, axiom,
% 5.50/5.71    (![A:$i,B:$i,C:$i]:
% 5.50/5.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 5.50/5.71       ( r1_tarski @ A @ C ) ))).
% 5.50/5.71  thf('69', plain,
% 5.50/5.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.50/5.71         (~ (r1_tarski @ X5 @ X6)
% 5.50/5.71          | ~ (r1_tarski @ X6 @ X7)
% 5.50/5.71          | (r1_tarski @ X5 @ X7))),
% 5.50/5.71      inference('cnf', [status(esa)], [t1_xboole_1])).
% 5.50/5.71  thf('70', plain,
% 5.50/5.71      (![X0 : $i, X1 : $i]:
% 5.50/5.71         (~ (v1_relat_1 @ X0)
% 5.50/5.71          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 5.50/5.71          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1))),
% 5.50/5.71      inference('sup-', [status(thm)], ['68', '69'])).
% 5.50/5.71  thf('71', plain,
% 5.50/5.71      ((~ (v1_relat_1 @ sk_C)
% 5.50/5.71        | ~ (v1_funct_1 @ sk_C)
% 5.50/5.71        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 5.50/5.71        | ~ (v1_relat_1 @ sk_C))),
% 5.50/5.71      inference('sup-', [status(thm)], ['60', '70'])).
% 5.50/5.71  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 5.50/5.71      inference('demod', [status(thm)], ['27', '28'])).
% 5.50/5.71  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 5.50/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.71  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 5.50/5.71      inference('demod', [status(thm)], ['27', '28'])).
% 5.50/5.71  thf('75', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 5.50/5.71      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 5.50/5.71  thf('76', plain, ($false), inference('demod', [status(thm)], ['59', '75'])).
% 5.50/5.71  
% 5.50/5.71  % SZS output end Refutation
% 5.50/5.71  
% 5.50/5.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
