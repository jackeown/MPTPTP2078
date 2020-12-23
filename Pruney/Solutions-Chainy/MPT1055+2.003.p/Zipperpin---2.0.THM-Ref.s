%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.znFs5Sb22L

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 213 expanded)
%              Number of leaves         :   44 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  911 (3346 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      = sk_D )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      = sk_D )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf(t149_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X14 @ X16 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t149_funct_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['6','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['5','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['8'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['8'])).

thf('36',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ),
    inference('sat_resolution*',[status(thm)],['6','29','35'])).

thf('37',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('48',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','57'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X18 @ X17 ) @ X19 )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['37','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['31','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.znFs5Sb22L
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.89/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.89/2.11  % Solved by: fo/fo7.sh
% 1.89/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.89/2.11  % done 1105 iterations in 1.638s
% 1.89/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.89/2.11  % SZS output start Refutation
% 1.89/2.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.89/2.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.89/2.11  thf(sk_C_type, type, sk_C: $i).
% 1.89/2.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.89/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.89/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.89/2.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.89/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.89/2.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.89/2.11  thf(sk_E_type, type, sk_E: $i).
% 1.89/2.11  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.89/2.11  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.89/2.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.89/2.11  thf(sk_D_type, type, sk_D: $i).
% 1.89/2.11  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.89/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.89/2.11  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.89/2.11  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.89/2.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.89/2.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.89/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.89/2.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.89/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.89/2.11  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.89/2.11  thf(t172_funct_2, conjecture,
% 1.89/2.11    (![A:$i]:
% 1.89/2.11     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.89/2.11       ( ![B:$i]:
% 1.89/2.11         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.89/2.11           ( ![C:$i]:
% 1.89/2.11             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.89/2.11                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.89/2.11               ( ![D:$i]:
% 1.89/2.11                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.11                   ( ![E:$i]:
% 1.89/2.11                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.89/2.11                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.89/2.11                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.89/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.89/2.11    (~( ![A:$i]:
% 1.89/2.11        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.89/2.11          ( ![B:$i]:
% 1.89/2.11            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.89/2.11              ( ![C:$i]:
% 1.89/2.11                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.89/2.11                    ( m1_subset_1 @
% 1.89/2.11                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.89/2.11                  ( ![D:$i]:
% 1.89/2.11                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.11                      ( ![E:$i]:
% 1.89/2.11                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.89/2.11                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.89/2.11                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.89/2.11    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 1.89/2.11  thf('0', plain,
% 1.89/2.11      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.89/2.11        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf('1', plain,
% 1.89/2.11      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.89/2.11         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('split', [status(esa)], ['0'])).
% 1.89/2.11  thf('2', plain,
% 1.89/2.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(redefinition_k8_relset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.89/2.11  thf('3', plain,
% 1.89/2.11      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.89/2.11         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.89/2.11          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 1.89/2.11      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.89/2.11  thf('4', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['2', '3'])).
% 1.89/2.11  thf('5', plain,
% 1.89/2.11      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.89/2.11         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('demod', [status(thm)], ['1', '4'])).
% 1.89/2.11  thf('6', plain,
% 1.89/2.11      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.89/2.11       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.89/2.11      inference('split', [status(esa)], ['0'])).
% 1.89/2.11  thf('7', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['2', '3'])).
% 1.89/2.11  thf('8', plain,
% 1.89/2.11      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.89/2.11        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf('9', plain,
% 1.89/2.11      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.89/2.11         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('split', [status(esa)], ['8'])).
% 1.89/2.11  thf(t28_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.89/2.11  thf('10', plain,
% 1.89/2.11      (![X5 : $i, X6 : $i]:
% 1.89/2.11         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 1.89/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.89/2.11  thf('11', plain,
% 1.89/2.11      ((((k3_xboole_0 @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.89/2.11          = (sk_D)))
% 1.89/2.11         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('sup-', [status(thm)], ['9', '10'])).
% 1.89/2.11  thf('12', plain,
% 1.89/2.11      ((((k3_xboole_0 @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)) = (sk_D)))
% 1.89/2.11         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('sup+', [status(thm)], ['7', '11'])).
% 1.89/2.11  thf(t149_funct_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.89/2.11       ( r1_tarski @
% 1.89/2.11         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 1.89/2.11         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 1.89/2.11  thf('13', plain,
% 1.89/2.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.89/2.11         ((r1_tarski @ 
% 1.89/2.11           (k9_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ (k10_relat_1 @ X14 @ X16))) @ 
% 1.89/2.11           (k3_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ X16))
% 1.89/2.11          | ~ (v1_funct_1 @ X14)
% 1.89/2.11          | ~ (v1_relat_1 @ X14))),
% 1.89/2.11      inference('cnf', [status(esa)], [t149_funct_1])).
% 1.89/2.11  thf(commutativity_k3_xboole_0, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.89/2.11  thf('14', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.89/2.11  thf(t18_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.89/2.11  thf('15', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.89/2.11         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.89/2.11  thf('16', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.11         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['14', '15'])).
% 1.89/2.11  thf('17', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.11         (~ (v1_relat_1 @ X2)
% 1.89/2.11          | ~ (v1_funct_1 @ X2)
% 1.89/2.11          | (r1_tarski @ 
% 1.89/2.11             (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ (k10_relat_1 @ X2 @ X0))) @ 
% 1.89/2.11             X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['13', '16'])).
% 1.89/2.11  thf('18', plain,
% 1.89/2.11      ((((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 1.89/2.11         | ~ (v1_funct_1 @ sk_C)
% 1.89/2.11         | ~ (v1_relat_1 @ sk_C)))
% 1.89/2.11         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('sup+', [status(thm)], ['12', '17'])).
% 1.89/2.11  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf('20', plain,
% 1.89/2.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(cc1_relset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( v1_relat_1 @ C ) ))).
% 1.89/2.11  thf('21', plain,
% 1.89/2.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.89/2.11         ((v1_relat_1 @ X20)
% 1.89/2.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.89/2.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.89/2.11  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 1.89/2.11      inference('sup-', [status(thm)], ['20', '21'])).
% 1.89/2.11  thf('23', plain,
% 1.89/2.11      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.89/2.11         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.89/2.11      inference('demod', [status(thm)], ['18', '19', '22'])).
% 1.89/2.11  thf('24', plain,
% 1.89/2.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(redefinition_k7_relset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.89/2.11  thf('25', plain,
% 1.89/2.11      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.89/2.11         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.89/2.11          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 1.89/2.11      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.89/2.11  thf('26', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['24', '25'])).
% 1.89/2.11  thf('27', plain,
% 1.89/2.11      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.89/2.11         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.89/2.11      inference('split', [status(esa)], ['0'])).
% 1.89/2.11  thf('28', plain,
% 1.89/2.11      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.89/2.11         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['26', '27'])).
% 1.89/2.11  thf('29', plain,
% 1.89/2.11      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.89/2.11       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['23', '28'])).
% 1.89/2.11  thf('30', plain,
% 1.89/2.11      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.89/2.11      inference('sat_resolution*', [status(thm)], ['6', '29'])).
% 1.89/2.11  thf('31', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 1.89/2.11      inference('simpl_trail', [status(thm)], ['5', '30'])).
% 1.89/2.11  thf('32', plain,
% 1.89/2.11      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.89/2.11         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.89/2.11      inference('split', [status(esa)], ['8'])).
% 1.89/2.11  thf('33', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['24', '25'])).
% 1.89/2.11  thf('34', plain,
% 1.89/2.11      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.89/2.11         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.89/2.11      inference('demod', [status(thm)], ['32', '33'])).
% 1.89/2.11  thf('35', plain,
% 1.89/2.11      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.89/2.11       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.89/2.11      inference('split', [status(esa)], ['8'])).
% 1.89/2.11  thf('36', plain,
% 1.89/2.11      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.89/2.11      inference('sat_resolution*', [status(thm)], ['6', '29', '35'])).
% 1.89/2.11  thf('37', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 1.89/2.11      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 1.89/2.11  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(d1_funct_2, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.89/2.11           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.89/2.11             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.89/2.11         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.89/2.11           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.89/2.11             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.89/2.11  thf(zf_stmt_1, axiom,
% 1.89/2.11    (![C:$i,B:$i,A:$i]:
% 1.89/2.11     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.89/2.11       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.89/2.11  thf('39', plain,
% 1.89/2.11      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.89/2.11         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 1.89/2.11          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 1.89/2.11          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.89/2.11  thf('40', plain,
% 1.89/2.11      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.89/2.11        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['38', '39'])).
% 1.89/2.11  thf('41', plain,
% 1.89/2.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(redefinition_k1_relset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.89/2.11  thf('42', plain,
% 1.89/2.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.89/2.11         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.89/2.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.89/2.11      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.89/2.11  thf('43', plain,
% 1.89/2.11      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.89/2.11      inference('sup-', [status(thm)], ['41', '42'])).
% 1.89/2.11  thf('44', plain,
% 1.89/2.11      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.89/2.11      inference('demod', [status(thm)], ['40', '43'])).
% 1.89/2.11  thf(zf_stmt_2, axiom,
% 1.89/2.11    (![B:$i,A:$i]:
% 1.89/2.11     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.89/2.11       ( zip_tseitin_0 @ B @ A ) ))).
% 1.89/2.11  thf('45', plain,
% 1.89/2.11      (![X37 : $i, X38 : $i]:
% 1.89/2.11         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.89/2.11  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.89/2.11  thf('46', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.89/2.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.89/2.11  thf('47', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.11         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.89/2.11      inference('sup+', [status(thm)], ['45', '46'])).
% 1.89/2.11  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.89/2.11  thf('48', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 1.89/2.11      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.89/2.11  thf(t69_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.89/2.11       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.89/2.11  thf('49', plain,
% 1.89/2.11      (![X9 : $i, X10 : $i]:
% 1.89/2.11         (~ (r1_xboole_0 @ X9 @ X10)
% 1.89/2.11          | ~ (r1_tarski @ X9 @ X10)
% 1.89/2.11          | (v1_xboole_0 @ X9))),
% 1.89/2.11      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.89/2.11  thf('50', plain,
% 1.89/2.11      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['48', '49'])).
% 1.89/2.11  thf('51', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 1.89/2.11      inference('sup-', [status(thm)], ['47', '50'])).
% 1.89/2.11  thf('52', plain,
% 1.89/2.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.89/2.11  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.89/2.11  thf(zf_stmt_5, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.11       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.89/2.11         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.89/2.11           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.89/2.11             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.89/2.11  thf('53', plain,
% 1.89/2.11      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.89/2.11         (~ (zip_tseitin_0 @ X42 @ X43)
% 1.89/2.11          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 1.89/2.11          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.89/2.11  thf('54', plain,
% 1.89/2.11      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.89/2.11      inference('sup-', [status(thm)], ['52', '53'])).
% 1.89/2.11  thf('55', plain,
% 1.89/2.11      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.89/2.11      inference('sup-', [status(thm)], ['51', '54'])).
% 1.89/2.11  thf('56', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf('57', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.89/2.11      inference('clc', [status(thm)], ['55', '56'])).
% 1.89/2.11  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.89/2.11      inference('demod', [status(thm)], ['44', '57'])).
% 1.89/2.11  thf(t163_funct_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.89/2.11       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.89/2.11           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.89/2.11         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.89/2.11  thf('59', plain,
% 1.89/2.11      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.89/2.11         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 1.89/2.11          | ~ (r1_tarski @ (k9_relat_1 @ X18 @ X17) @ X19)
% 1.89/2.11          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ X19))
% 1.89/2.11          | ~ (v1_funct_1 @ X18)
% 1.89/2.11          | ~ (v1_relat_1 @ X18))),
% 1.89/2.11      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.89/2.11  thf('60', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         (~ (r1_tarski @ X0 @ sk_A)
% 1.89/2.11          | ~ (v1_relat_1 @ sk_C)
% 1.89/2.11          | ~ (v1_funct_1 @ sk_C)
% 1.89/2.11          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 1.89/2.11          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 1.89/2.11      inference('sup-', [status(thm)], ['58', '59'])).
% 1.89/2.11  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 1.89/2.11      inference('sup-', [status(thm)], ['20', '21'])).
% 1.89/2.11  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf('63', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         (~ (r1_tarski @ X0 @ sk_A)
% 1.89/2.11          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 1.89/2.11          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 1.89/2.11      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.89/2.11  thf('64', plain,
% 1.89/2.11      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.89/2.11        | ~ (r1_tarski @ sk_D @ sk_A))),
% 1.89/2.11      inference('sup-', [status(thm)], ['37', '63'])).
% 1.89/2.11  thf('65', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(t3_subset, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.89/2.11  thf('66', plain,
% 1.89/2.11      (![X11 : $i, X12 : $i]:
% 1.89/2.11         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t3_subset])).
% 1.89/2.11  thf('67', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.89/2.11      inference('sup-', [status(thm)], ['65', '66'])).
% 1.89/2.11  thf('68', plain, ((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 1.89/2.11      inference('demod', [status(thm)], ['64', '67'])).
% 1.89/2.11  thf('69', plain, ($false), inference('demod', [status(thm)], ['31', '68'])).
% 1.89/2.11  
% 1.89/2.11  % SZS output end Refutation
% 1.89/2.11  
% 1.95/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
