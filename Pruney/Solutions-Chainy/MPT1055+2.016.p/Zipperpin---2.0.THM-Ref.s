%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f0esLG5qaI

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:36 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 280 expanded)
%              Number of leaves         :   39 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          : 1064 (4448 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['7'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( ( k2_xboole_0 @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      = ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X18 ) @ ( k9_relat_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('34',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['26','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['7'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ),
    inference('sat_resolution*',[status(thm)],['8','38','39'])).

thf('41',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X43 @ X44 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X46 ) ) )
      | ( r1_tarski @ X43 @ ( k8_relset_1 @ X44 @ X46 @ X45 @ ( k7_relset_1 @ X44 @ X46 @ X45 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_funct_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('53',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k8_relset_1 @ X40 @ X41 @ X42 @ ( k7_relset_1 @ X40 @ X41 @ X42 @ X40 ) )
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('54',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X24 @ X23 ) @ X25 )
      | ( r1_tarski @ X23 @ ( k10_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['7'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['8','38'])).

thf('80',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['75','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f0esLG5qaI
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.51/1.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.76  % Solved by: fo/fo7.sh
% 1.51/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.76  % done 2649 iterations in 1.302s
% 1.51/1.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.76  % SZS output start Refutation
% 1.51/1.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.76  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.51/1.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.51/1.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.51/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.76  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.51/1.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.76  thf(sk_E_type, type, sk_E: $i).
% 1.51/1.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.76  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.51/1.76  thf(t172_funct_2, conjecture,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.51/1.76       ( ![B:$i]:
% 1.51/1.76         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.51/1.76           ( ![C:$i]:
% 1.51/1.76             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.76                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.76               ( ![D:$i]:
% 1.51/1.76                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.76                   ( ![E:$i]:
% 1.51/1.76                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.51/1.76                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.51/1.76                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.51/1.76  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.76    (~( ![A:$i]:
% 1.51/1.76        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.51/1.76          ( ![B:$i]:
% 1.51/1.76            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.51/1.76              ( ![C:$i]:
% 1.51/1.76                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.76                    ( m1_subset_1 @
% 1.51/1.76                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.76                  ( ![D:$i]:
% 1.51/1.76                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.76                      ( ![E:$i]:
% 1.51/1.76                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.51/1.76                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.51/1.76                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.51/1.76    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 1.51/1.76  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('1', plain,
% 1.51/1.76      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.51/1.76        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('2', plain,
% 1.51/1.76      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.51/1.76         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.51/1.76      inference('split', [status(esa)], ['1'])).
% 1.51/1.76  thf('3', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(redefinition_k7_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.51/1.76  thf('4', plain,
% 1.51/1.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.51/1.76         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.51/1.76          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.51/1.76  thf('5', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.76  thf('6', plain,
% 1.51/1.76      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.51/1.76         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.51/1.76      inference('demod', [status(thm)], ['2', '5'])).
% 1.51/1.76  thf('7', plain,
% 1.51/1.76      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.51/1.76        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('8', plain,
% 1.51/1.76      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.51/1.76       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.51/1.76      inference('split', [status(esa)], ['7'])).
% 1.51/1.76  thf(t145_funct_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.51/1.76       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.51/1.76  thf('9', plain,
% 1.51/1.76      (![X21 : $i, X22 : $i]:
% 1.51/1.76         ((r1_tarski @ (k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X22)) @ X22)
% 1.51/1.76          | ~ (v1_funct_1 @ X21)
% 1.51/1.76          | ~ (v1_relat_1 @ X21))),
% 1.51/1.76      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.51/1.76  thf('10', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(redefinition_k8_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.51/1.76  thf('11', plain,
% 1.51/1.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.51/1.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.51/1.76          | ((k8_relset_1 @ X34 @ X35 @ X33 @ X36) = (k10_relat_1 @ X33 @ X36)))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.51/1.76  thf('12', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('13', plain,
% 1.51/1.76      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('split', [status(esa)], ['1'])).
% 1.51/1.76  thf('14', plain,
% 1.51/1.76      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('sup+', [status(thm)], ['12', '13'])).
% 1.51/1.76  thf(t12_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.51/1.76  thf('15', plain,
% 1.51/1.76      (![X6 : $i, X7 : $i]:
% 1.51/1.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.76  thf('16', plain,
% 1.51/1.76      ((((k2_xboole_0 @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.51/1.76          = (k10_relat_1 @ sk_C @ sk_E)))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['14', '15'])).
% 1.51/1.76  thf(d10_xboole_0, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.76  thf('17', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.51/1.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.76  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.51/1.76      inference('simplify', [status(thm)], ['17'])).
% 1.51/1.76  thf(t11_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.51/1.76  thf('19', plain,
% 1.51/1.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.76         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.51/1.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.51/1.76  thf('20', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.76  thf(t156_relat_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( v1_relat_1 @ C ) =>
% 1.51/1.76       ( ( r1_tarski @ A @ B ) =>
% 1.51/1.76         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.51/1.76  thf('21', plain,
% 1.51/1.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.76         (~ (r1_tarski @ X18 @ X19)
% 1.51/1.76          | ~ (v1_relat_1 @ X20)
% 1.51/1.76          | (r1_tarski @ (k9_relat_1 @ X20 @ X18) @ (k9_relat_1 @ X20 @ X19)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.51/1.76  thf('22', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 1.51/1.76           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.51/1.76          | ~ (v1_relat_1 @ X2))),
% 1.51/1.76      inference('sup-', [status(thm)], ['20', '21'])).
% 1.51/1.76  thf(t1_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.51/1.76       ( r1_tarski @ A @ C ) ))).
% 1.51/1.76  thf('23', plain,
% 1.51/1.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.76         (~ (r1_tarski @ X8 @ X9)
% 1.51/1.76          | ~ (r1_tarski @ X9 @ X10)
% 1.51/1.76          | (r1_tarski @ X8 @ X10))),
% 1.51/1.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.51/1.76  thf('24', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.51/1.76         (~ (v1_relat_1 @ X2)
% 1.51/1.76          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3)
% 1.51/1.76          | ~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 1.51/1.76      inference('sup-', [status(thm)], ['22', '23'])).
% 1.51/1.76  thf('25', plain,
% 1.51/1.76      ((![X0 : $i, X1 : $i]:
% 1.51/1.76          (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ sk_E)) @ X0)
% 1.51/1.76           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_D) @ X0)
% 1.51/1.76           | ~ (v1_relat_1 @ X1)))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['16', '24'])).
% 1.51/1.76  thf('26', plain,
% 1.51/1.76      (((~ (v1_relat_1 @ sk_C)
% 1.51/1.76         | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76         | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['9', '25'])).
% 1.51/1.76  thf('27', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(cc2_relat_1, axiom,
% 1.51/1.76    (![A:$i]:
% 1.51/1.76     ( ( v1_relat_1 @ A ) =>
% 1.51/1.76       ( ![B:$i]:
% 1.51/1.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.51/1.76  thf('28', plain,
% 1.51/1.76      (![X14 : $i, X15 : $i]:
% 1.51/1.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.51/1.76          | (v1_relat_1 @ X14)
% 1.51/1.76          | ~ (v1_relat_1 @ X15))),
% 1.51/1.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.51/1.76  thf('29', plain,
% 1.51/1.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.51/1.76      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.76  thf(fc6_relat_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.51/1.76  thf('30', plain,
% 1.51/1.76      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 1.51/1.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.51/1.76  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('demod', [status(thm)], ['29', '30'])).
% 1.51/1.76  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('demod', [status(thm)], ['29', '30'])).
% 1.51/1.76  thf('34', plain,
% 1.51/1.76      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.51/1.76         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('demod', [status(thm)], ['26', '31', '32', '33'])).
% 1.51/1.76  thf('35', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.76  thf('36', plain,
% 1.51/1.76      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.51/1.76         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.51/1.76      inference('split', [status(esa)], ['7'])).
% 1.51/1.76  thf('37', plain,
% 1.51/1.76      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.51/1.76         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['35', '36'])).
% 1.51/1.76  thf('38', plain,
% 1.51/1.76      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.51/1.76       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['34', '37'])).
% 1.51/1.76  thf('39', plain,
% 1.51/1.76      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.51/1.76       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.51/1.76      inference('split', [status(esa)], ['1'])).
% 1.51/1.76  thf('40', plain,
% 1.51/1.76      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.51/1.76      inference('sat_resolution*', [status(thm)], ['8', '38', '39'])).
% 1.51/1.76  thf('41', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 1.51/1.76      inference('simpl_trail', [status(thm)], ['6', '40'])).
% 1.51/1.76  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.51/1.76      inference('simplify', [status(thm)], ['17'])).
% 1.51/1.76  thf('43', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(t50_funct_2, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.51/1.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.76       ( ( r1_tarski @ C @ A ) =>
% 1.51/1.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.51/1.76           ( r1_tarski @
% 1.51/1.76             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 1.51/1.76  thf('44', plain,
% 1.51/1.76      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.51/1.76         (~ (r1_tarski @ X43 @ X44)
% 1.51/1.76          | ((X46) = (k1_xboole_0))
% 1.51/1.76          | ~ (v1_funct_1 @ X45)
% 1.51/1.76          | ~ (v1_funct_2 @ X45 @ X44 @ X46)
% 1.51/1.76          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X46)))
% 1.51/1.76          | (r1_tarski @ X43 @ 
% 1.51/1.76             (k8_relset_1 @ X44 @ X46 @ X45 @ 
% 1.51/1.76              (k7_relset_1 @ X44 @ X46 @ X45 @ X43))))),
% 1.51/1.76      inference('cnf', [status(esa)], [t50_funct_2])).
% 1.51/1.76  thf('45', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((r1_tarski @ X0 @ 
% 1.51/1.76           (k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 1.51/1.76            (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0)))
% 1.51/1.76          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.51/1.76          | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76          | ((sk_B) = (k1_xboole_0))
% 1.51/1.76          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['43', '44'])).
% 1.51/1.76  thf('46', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.76  thf('47', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('50', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)))
% 1.51/1.76          | ((sk_B) = (k1_xboole_0))
% 1.51/1.76          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.51/1.76      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 1.51/1.76  thf('51', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0))
% 1.51/1.76        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 1.51/1.76      inference('sup-', [status(thm)], ['42', '50'])).
% 1.51/1.76  thf('52', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(t39_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.51/1.76       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 1.51/1.76           ( k2_relset_1 @ B @ A @ C ) ) & 
% 1.51/1.76         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 1.51/1.76           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 1.51/1.76  thf('53', plain,
% 1.51/1.76      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.51/1.76         (((k8_relset_1 @ X40 @ X41 @ X42 @ 
% 1.51/1.76            (k7_relset_1 @ X40 @ X41 @ X42 @ X40))
% 1.51/1.76            = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.51/1.76          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 1.51/1.76      inference('cnf', [status(esa)], [t39_relset_1])).
% 1.51/1.76  thf('54', plain,
% 1.51/1.76      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 1.51/1.76         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 1.51/1.76         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 1.51/1.76      inference('sup-', [status(thm)], ['52', '53'])).
% 1.51/1.76  thf('55', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.76  thf('56', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('57', plain,
% 1.51/1.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.76  thf('58', plain,
% 1.51/1.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.51/1.76         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.51/1.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.51/1.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.76  thf('59', plain,
% 1.51/1.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('sup-', [status(thm)], ['57', '58'])).
% 1.51/1.76  thf('60', plain,
% 1.51/1.76      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.51/1.76      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 1.51/1.76  thf('61', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('demod', [status(thm)], ['51', '60'])).
% 1.51/1.76  thf('62', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(t3_subset, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.76  thf('63', plain,
% 1.51/1.76      (![X11 : $i, X12 : $i]:
% 1.51/1.76         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.76  thf('64', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.51/1.76      inference('sup-', [status(thm)], ['62', '63'])).
% 1.51/1.76  thf('65', plain,
% 1.51/1.76      (![X6 : $i, X7 : $i]:
% 1.51/1.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.51/1.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.76  thf('66', plain, (((k2_xboole_0 @ sk_D @ sk_A) = (sk_A))),
% 1.51/1.76      inference('sup-', [status(thm)], ['64', '65'])).
% 1.51/1.76  thf('67', plain,
% 1.51/1.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.76         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.51/1.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.51/1.76  thf('68', plain,
% 1.51/1.76      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_D @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['66', '67'])).
% 1.51/1.76  thf('69', plain,
% 1.51/1.76      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['61', '68'])).
% 1.51/1.76  thf(t163_funct_1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i]:
% 1.51/1.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.51/1.76       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.51/1.76           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.51/1.76         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.51/1.76  thf('70', plain,
% 1.51/1.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.51/1.76         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 1.51/1.76          | ~ (r1_tarski @ (k9_relat_1 @ X24 @ X23) @ X25)
% 1.51/1.76          | (r1_tarski @ X23 @ (k10_relat_1 @ X24 @ X25))
% 1.51/1.76          | ~ (v1_funct_1 @ X24)
% 1.51/1.76          | ~ (v1_relat_1 @ X24))),
% 1.51/1.76      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.51/1.76  thf('71', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (((sk_B) = (k1_xboole_0))
% 1.51/1.76          | ~ (v1_relat_1 @ sk_C)
% 1.51/1.76          | ~ (v1_funct_1 @ sk_C)
% 1.51/1.76          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.51/1.76          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['69', '70'])).
% 1.51/1.76  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.76      inference('demod', [status(thm)], ['29', '30'])).
% 1.51/1.76  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('74', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         (((sk_B) = (k1_xboole_0))
% 1.51/1.76          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.51/1.76          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.51/1.76      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.51/1.76  thf('75', plain,
% 1.51/1.76      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.51/1.76        | ((sk_B) = (k1_xboole_0)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['41', '74'])).
% 1.51/1.76  thf('76', plain,
% 1.51/1.76      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.51/1.76         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('split', [status(esa)], ['7'])).
% 1.51/1.76  thf('77', plain,
% 1.51/1.76      (![X0 : $i]:
% 1.51/1.76         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('78', plain,
% 1.51/1.76      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.51/1.76         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.51/1.76      inference('demod', [status(thm)], ['76', '77'])).
% 1.51/1.76  thf('79', plain,
% 1.51/1.76      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.51/1.76      inference('sat_resolution*', [status(thm)], ['8', '38'])).
% 1.51/1.76  thf('80', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 1.51/1.76      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 1.51/1.76  thf('81', plain, (((sk_B) = (k1_xboole_0))),
% 1.51/1.76      inference('clc', [status(thm)], ['75', '80'])).
% 1.51/1.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.51/1.76  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.76  thf('83', plain, ($false),
% 1.51/1.76      inference('demod', [status(thm)], ['0', '81', '82'])).
% 1.51/1.76  
% 1.51/1.76  % SZS output end Refutation
% 1.51/1.76  
% 1.51/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
