%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UkEVKXyDm1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 295 expanded)
%              Number of leaves         :   36 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  877 (4883 expanded)
%              Number of equality atoms :   26 (  68 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( ( k8_relset_1 @ X33 @ X35 @ X34 @ X35 )
        = X33 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X18 @ X17 ) @ X19 )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('46',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['44','51'])).

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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('57',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['57'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X12 @ X10 ) @ ( k9_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['52'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

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
    inference('sup-',[status(thm)],['25','26'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('71',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['55','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UkEVKXyDm1
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.60/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.79  % Solved by: fo/fo7.sh
% 1.60/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.79  % done 2496 iterations in 1.342s
% 1.60/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.79  % SZS output start Refutation
% 1.60/1.79  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.60/1.79  thf(sk_B_type, type, sk_B: $i > $i).
% 1.60/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.60/1.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.79  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.60/1.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.79  thf(sk_E_type, type, sk_E: $i).
% 1.60/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.60/1.79  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.60/1.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.79  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.60/1.79  thf(t172_funct_2, conjecture,
% 1.60/1.79    (![A:$i]:
% 1.60/1.79     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.60/1.79       ( ![B:$i]:
% 1.60/1.79         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.60/1.79           ( ![C:$i]:
% 1.60/1.79             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.79                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.79               ( ![D:$i]:
% 1.60/1.79                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79                   ( ![E:$i]:
% 1.60/1.79                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.60/1.79                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.60/1.79                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.60/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.79    (~( ![A:$i]:
% 1.60/1.79        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.60/1.79          ( ![B:$i]:
% 1.60/1.79            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.60/1.79              ( ![C:$i]:
% 1.60/1.79                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.79                    ( m1_subset_1 @
% 1.60/1.79                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.79                  ( ![D:$i]:
% 1.60/1.79                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79                      ( ![E:$i]:
% 1.60/1.79                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.60/1.79                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.60/1.79                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.60/1.79    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 1.60/1.79  thf('0', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 1.60/1.79        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('1', plain,
% 1.60/1.79      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('2', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(redefinition_k7_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.60/1.79  thf('3', plain,
% 1.60/1.79      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.60/1.79          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.60/1.79  thf('4', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.79  thf('5', plain,
% 1.60/1.79      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)))),
% 1.60/1.79      inference('demod', [status(thm)], ['1', '4'])).
% 1.60/1.79  thf('6', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 1.60/1.79        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('7', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(redefinition_k8_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.60/1.79  thf('8', plain,
% 1.60/1.79      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.79          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.60/1.79  thf('9', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf('10', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.79  thf('11', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.60/1.79        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))),
% 1.60/1.79      inference('demod', [status(thm)], ['6', '9', '10'])).
% 1.60/1.79  thf('12', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf('13', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('14', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['12', '13'])).
% 1.60/1.79  thf('15', plain,
% 1.60/1.79      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['11', '14'])).
% 1.60/1.79  thf('16', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(t48_funct_2, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.79         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 1.60/1.79  thf('17', plain,
% 1.60/1.79      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.60/1.79         (((X35) = (k1_xboole_0))
% 1.60/1.79          | ~ (v1_funct_1 @ X34)
% 1.60/1.79          | ~ (v1_funct_2 @ X34 @ X33 @ X35)
% 1.60/1.79          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X35)))
% 1.60/1.79          | ((k8_relset_1 @ X33 @ X35 @ X34 @ X35) = (X33)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t48_funct_2])).
% 1.60/1.79  thf('18', plain,
% 1.60/1.79      ((((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_B_1) = (sk_A))
% 1.60/1.79        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 1.60/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.79        | ((sk_B_1) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['16', '17'])).
% 1.60/1.79  thf('19', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf('20', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('22', plain,
% 1.60/1.79      ((((k10_relat_1 @ sk_C @ sk_B_1) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.60/1.79      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 1.60/1.79  thf(t167_relat_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( v1_relat_1 @ B ) =>
% 1.60/1.79       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.60/1.79  thf('23', plain,
% 1.60/1.79      (![X13 : $i, X14 : $i]:
% 1.60/1.79         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 1.60/1.79          | ~ (v1_relat_1 @ X13))),
% 1.60/1.79      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.60/1.79  thf('24', plain,
% 1.60/1.79      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 1.60/1.79        | ((sk_B_1) = (k1_xboole_0))
% 1.60/1.79        | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.79      inference('sup+', [status(thm)], ['22', '23'])).
% 1.60/1.79  thf('25', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(cc1_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( v1_relat_1 @ C ) ))).
% 1.60/1.79  thf('26', plain,
% 1.60/1.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.60/1.79         ((v1_relat_1 @ X22)
% 1.60/1.79          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.60/1.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.79  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.79      inference('sup-', [status(thm)], ['25', '26'])).
% 1.60/1.79  thf('28', plain,
% 1.60/1.79      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.60/1.79      inference('demod', [status(thm)], ['24', '27'])).
% 1.60/1.79  thf('29', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(t3_subset, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.60/1.79  thf('30', plain,
% 1.60/1.79      (![X7 : $i, X8 : $i]:
% 1.60/1.79         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.79  thf('31', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.60/1.79      inference('sup-', [status(thm)], ['29', '30'])).
% 1.60/1.79  thf(t1_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.60/1.79       ( r1_tarski @ A @ C ) ))).
% 1.60/1.79  thf('32', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79         (~ (r1_tarski @ X0 @ X1)
% 1.60/1.79          | ~ (r1_tarski @ X1 @ X2)
% 1.60/1.79          | (r1_tarski @ X0 @ X2))),
% 1.60/1.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.60/1.79  thf('33', plain,
% 1.60/1.79      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['31', '32'])).
% 1.60/1.79  thf('34', plain,
% 1.60/1.79      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['28', '33'])).
% 1.60/1.79  thf(t163_funct_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.60/1.79       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.60/1.79           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.60/1.79         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.60/1.79  thf('35', plain,
% 1.60/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.60/1.79         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 1.60/1.79          | ~ (r1_tarski @ (k9_relat_1 @ X18 @ X17) @ X19)
% 1.60/1.79          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ X19))
% 1.60/1.79          | ~ (v1_funct_1 @ X18)
% 1.60/1.79          | ~ (v1_relat_1 @ X18))),
% 1.60/1.79      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.60/1.79  thf('36', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         (((sk_B_1) = (k1_xboole_0))
% 1.60/1.79          | ~ (v1_relat_1 @ sk_C)
% 1.60/1.79          | ~ (v1_funct_1 @ sk_C)
% 1.60/1.79          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.60/1.79          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['34', '35'])).
% 1.60/1.79  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.79      inference('sup-', [status(thm)], ['25', '26'])).
% 1.60/1.79  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('39', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         (((sk_B_1) = (k1_xboole_0))
% 1.60/1.79          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.60/1.79          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.60/1.79      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.60/1.79  thf('40', plain,
% 1.60/1.79      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.60/1.79         | ((sk_B_1) = (k1_xboole_0))))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['15', '39'])).
% 1.60/1.79  thf('41', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['12', '13'])).
% 1.60/1.79  thf('42', plain,
% 1.60/1.79      ((((sk_B_1) = (k1_xboole_0)))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('clc', [status(thm)], ['40', '41'])).
% 1.60/1.79  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('44', plain,
% 1.60/1.79      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.60/1.79         <= (~
% 1.60/1.79             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['42', '43'])).
% 1.60/1.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.60/1.79  thf('45', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.60/1.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.79  thf(existence_m1_subset_1, axiom,
% 1.60/1.79    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.60/1.79  thf('46', plain, (![X4 : $i]: (m1_subset_1 @ (sk_B @ X4) @ X4)),
% 1.60/1.79      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.60/1.79  thf(t2_subset, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ A @ B ) =>
% 1.60/1.79       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.60/1.79  thf('47', plain,
% 1.60/1.79      (![X5 : $i, X6 : $i]:
% 1.60/1.79         ((r2_hidden @ X5 @ X6)
% 1.60/1.79          | (v1_xboole_0 @ X6)
% 1.60/1.79          | ~ (m1_subset_1 @ X5 @ X6))),
% 1.60/1.79      inference('cnf', [status(esa)], [t2_subset])).
% 1.60/1.79  thf('48', plain,
% 1.60/1.79      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.79  thf(t7_ordinal1, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.60/1.79  thf('49', plain,
% 1.60/1.79      (![X20 : $i, X21 : $i]:
% 1.60/1.79         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 1.60/1.79      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.60/1.79  thf('50', plain,
% 1.60/1.79      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['48', '49'])).
% 1.60/1.79  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.60/1.79      inference('sup-', [status(thm)], ['45', '50'])).
% 1.60/1.79  thf('52', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 1.60/1.79      inference('demod', [status(thm)], ['44', '51'])).
% 1.60/1.79  thf('53', plain,
% 1.60/1.79      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E)) | 
% 1.60/1.79       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('54', plain,
% 1.60/1.79      (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 1.60/1.79  thf('55', plain, (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['5', '54'])).
% 1.60/1.79  thf(t145_funct_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.60/1.79       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.60/1.79  thf('56', plain,
% 1.60/1.79      (![X15 : $i, X16 : $i]:
% 1.60/1.79         ((r1_tarski @ (k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X16)) @ X16)
% 1.60/1.79          | ~ (v1_funct_1 @ X15)
% 1.60/1.79          | ~ (v1_relat_1 @ X15))),
% 1.60/1.79      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.60/1.79  thf('57', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))
% 1.60/1.79        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_E))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('58', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.60/1.79         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('split', [status(esa)], ['57'])).
% 1.60/1.79  thf(t156_relat_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( v1_relat_1 @ C ) =>
% 1.60/1.79       ( ( r1_tarski @ A @ B ) =>
% 1.60/1.79         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.60/1.79  thf('59', plain,
% 1.60/1.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.60/1.79         (~ (r1_tarski @ X10 @ X11)
% 1.60/1.79          | ~ (v1_relat_1 @ X12)
% 1.60/1.79          | (r1_tarski @ (k9_relat_1 @ X12 @ X10) @ (k9_relat_1 @ X12 @ X11)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.60/1.79  thf('60', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.60/1.79            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['58', '59'])).
% 1.60/1.79  thf('61', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf('62', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.60/1.79            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))))),
% 1.60/1.79      inference('demod', [status(thm)], ['60', '61'])).
% 1.60/1.79  thf('63', plain,
% 1.60/1.79      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['52'])).
% 1.60/1.79  thf('64', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.60/1.79           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.60/1.79          | ~ (v1_relat_1 @ X0))),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 1.60/1.79  thf('65', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79         (~ (r1_tarski @ X0 @ X1)
% 1.60/1.79          | ~ (r1_tarski @ X1 @ X2)
% 1.60/1.79          | (r1_tarski @ X0 @ X2))),
% 1.60/1.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.60/1.79  thf('66', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         (~ (v1_relat_1 @ X0)
% 1.60/1.79          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 1.60/1.79          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1))),
% 1.60/1.79      inference('sup-', [status(thm)], ['64', '65'])).
% 1.60/1.79  thf('67', plain,
% 1.60/1.79      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.79        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.79        | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 1.60/1.79        | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.79      inference('sup-', [status(thm)], ['56', '66'])).
% 1.60/1.79  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.79      inference('sup-', [status(thm)], ['25', '26'])).
% 1.60/1.79  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.79      inference('sup-', [status(thm)], ['25', '26'])).
% 1.60/1.79  thf('71', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 1.60/1.79      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.60/1.79  thf('72', plain, ($false), inference('demod', [status(thm)], ['55', '71'])).
% 1.60/1.79  
% 1.60/1.79  % SZS output end Refutation
% 1.60/1.79  
% 1.60/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
