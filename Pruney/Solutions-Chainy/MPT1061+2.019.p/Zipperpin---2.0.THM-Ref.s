%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BGxsZ74liL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  147 (1196 expanded)
%              Number of leaves         :   42 ( 358 expanded)
%              Depth                    :   21
%              Number of atoms          : 1278 (23397 expanded)
%              Number of equality atoms :   52 ( 276 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k7_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k9_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['14','48','49'])).

thf('51',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','50'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['63','72','75'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['60','80'])).

thf('82',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','81'])).

thf('83',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','50'])).

thf('87',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','87'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf('91',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','87'])).

thf('92',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t130_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X38 )
       != X36 )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t130_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 )
    | ( ( k1_relset_1 @ sk_B @ k1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','81'])).

thf('99',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','87'])).

thf('100',plain,
    ( ( k1_relset_1 @ sk_B @ k1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['94','97','100'])).

thf('102',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['89','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BGxsZ74liL
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 191 iterations in 0.254s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.71  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.71  thf(t178_funct_2, conjecture,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.46/0.71       ( ![E:$i]:
% 0.46/0.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.46/0.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.46/0.71           ( ( ( r1_tarski @ B @ A ) & 
% 0.46/0.71               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.46/0.71             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.46/0.71               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.46/0.71               ( m1_subset_1 @
% 0.46/0.71                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.46/0.71                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71        ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.46/0.71          ( ![E:$i]:
% 0.46/0.71            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.46/0.71                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.46/0.71              ( ( ( r1_tarski @ B @ A ) & 
% 0.46/0.71                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.46/0.71                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.46/0.71                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.46/0.71                  ( m1_subset_1 @
% 0.46/0.71                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.46/0.71                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 0.46/0.71        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.46/0.71             sk_C)
% 0.46/0.71        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.46/0.71         <= (~
% 0.46/0.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.46/0.71               sk_C)))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k2_partfun1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.71          | ~ (v1_funct_1 @ X32)
% 0.46/0.71          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.46/0.71         <= (~
% 0.46/0.71             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.46/0.71               sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['1', '6'])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(dt_k2_partfun1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.46/0.71         ( m1_subset_1 @
% 0.46/0.71           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.46/0.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.71          | ~ (v1_funct_1 @ X28)
% 0.46/0.71          | (v1_funct_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31)))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 0.46/0.71         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('14', plain,
% 0.46/0.71      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('16', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.46/0.71          | ((k7_relset_1 @ X14 @ X15 @ X13 @ X16) = (k9_relat_1 @ X13 @ X16)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('19', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['15', '18'])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.71          | ~ (v1_funct_1 @ X28)
% 0.46/0.71          | (m1_subset_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.46/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 0.46/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.71  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.46/0.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.71  thf(cc2_relat_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.71          | (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 0.46/0.71          | (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.71  thf(fc6_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('30', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.71  thf(t148_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ B ) =>
% 0.46/0.71       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.71  thf('31', plain,
% 0.46/0.71      (![X4 : $i, X5 : $i]:
% 0.46/0.71         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.46/0.71          | ~ (v1_relat_1 @ X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.71  thf(t87_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ B ) =>
% 0.46/0.71       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      (![X6 : $i, X7 : $i]:
% 0.46/0.71         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X6 @ X7)) @ X7)
% 0.46/0.71          | ~ (v1_relat_1 @ X6))),
% 0.46/0.71      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.71  thf(t11_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ C ) =>
% 0.46/0.71       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.46/0.71           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.71         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.46/0.71          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.46/0.71          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.46/0.71          | ~ (v1_relat_1 @ X17))),
% 0.46/0.71      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X1)
% 0.46/0.71          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.71          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.46/0.71          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.46/0.71          | ~ (v1_relat_1 @ X1)
% 0.46/0.71          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.46/0.71          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ X1))),
% 0.46/0.71      inference('sup-', [status(thm)], ['31', '34'])).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.71          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.46/0.71          | ~ (v1_relat_1 @ X1)
% 0.46/0.71          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))),
% 0.46/0.71      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.46/0.71          | ~ (v1_relat_1 @ sk_E)
% 0.46/0.71          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['30', '36'])).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.71          | (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 0.46/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.71  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.46/0.71          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.46/0.71      inference('demod', [status(thm)], ['37', '42'])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['19', '43'])).
% 0.46/0.71  thf('45', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.46/0.71         <= (~
% 0.46/0.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('47', plain,
% 0.46/0.71      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.46/0.71         <= (~
% 0.46/0.71             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (~
% 0.46/0.71       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 0.46/0.71       ~
% 0.46/0.71       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.46/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 0.46/0.71       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      (~
% 0.46/0.71       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.46/0.71      inference('sat_resolution*', [status(thm)], ['14', '48', '49'])).
% 0.46/0.71  thf('51', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.46/0.71      inference('simpl_trail', [status(thm)], ['7', '50'])).
% 0.46/0.71  thf(d1_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_1, axiom,
% 0.46/0.71    (![B:$i,A:$i]:
% 0.46/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.71  thf('52', plain,
% 0.46/0.71      (![X20 : $i, X21 : $i]:
% 0.46/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.71  thf('53', plain,
% 0.46/0.71      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['19', '43'])).
% 0.46/0.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.71  thf(zf_stmt_3, axiom,
% 0.46/0.71    (![C:$i,B:$i,A:$i]:
% 0.46/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.71  thf(zf_stmt_5, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.71  thf('54', plain,
% 0.46/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.71         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.46/0.71          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.46/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.46/0.71        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.71  thf('56', plain,
% 0.46/0.71      ((((sk_C) = (k1_xboole_0))
% 0.46/0.71        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['52', '55'])).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['19', '43'])).
% 0.46/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.71  thf('58', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.46/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.71  thf('59', plain,
% 0.46/0.71      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 0.46/0.71         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.71  thf('60', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('61', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('62', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.71         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.46/0.71          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.46/0.71          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.71  thf('63', plain,
% 0.46/0.71      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 0.46/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      (![X20 : $i, X21 : $i]:
% 0.46/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.71  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.71      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.71         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.46/0.71          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.46/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.71  thf('69', plain,
% 0.46/0.71      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('70', plain,
% 0.46/0.71      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['66', '69'])).
% 0.46/0.71  thf('71', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('72', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 0.46/0.71      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.71  thf('73', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('74', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.46/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.46/0.71      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.71  thf('76', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 0.46/0.71      inference('demod', [status(thm)], ['63', '72', '75'])).
% 0.46/0.71  thf(t91_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ B ) =>
% 0.46/0.71       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.71         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.71  thf('77', plain,
% 0.46/0.71      (![X8 : $i, X9 : $i]:
% 0.46/0.71         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 0.46/0.71          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 0.46/0.71          | ~ (v1_relat_1 @ X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.46/0.71  thf('78', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_tarski @ X0 @ sk_A)
% 0.46/0.71          | ~ (v1_relat_1 @ sk_E)
% 0.46/0.71          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.71  thf('79', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.71  thf('80', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_tarski @ X0 @ sk_A)
% 0.46/0.71          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.71  thf('81', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['60', '80'])).
% 0.46/0.71  thf('82', plain,
% 0.46/0.71      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['59', '81'])).
% 0.46/0.71  thf('83', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.71         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.46/0.71          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.46/0.71          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      ((((sk_B) != (sk_B))
% 0.46/0.71        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.46/0.71        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.46/0.71        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.46/0.71      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.71  thf('86', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.46/0.71      inference('simpl_trail', [status(thm)], ['7', '50'])).
% 0.46/0.71  thf('87', plain,
% 0.46/0.71      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('88', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['56', '87'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.46/0.71      inference('demod', [status(thm)], ['51', '88'])).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['19', '43'])).
% 0.46/0.71  thf('91', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['56', '87'])).
% 0.46/0.71  thf('92', plain,
% 0.46/0.71      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.71  thf(t130_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.46/0.71         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.71           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.71  thf('93', plain,
% 0.46/0.71      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.71         (((k1_relset_1 @ X36 @ X37 @ X38) != (X36))
% 0.46/0.71          | (v1_funct_2 @ X38 @ X36 @ X37)
% 0.46/0.71          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.46/0.71          | ~ (v1_funct_1 @ X38))),
% 0.46/0.71      inference('cnf', [status(esa)], [t130_funct_2])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.46/0.71        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)
% 0.46/0.71        | ((k1_relset_1 @ sk_B @ k1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.46/0.71            != (sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.71  thf('95', plain,
% 0.46/0.71      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('97', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.71  thf('98', plain,
% 0.46/0.71      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['59', '81'])).
% 0.46/0.71  thf('99', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['56', '87'])).
% 0.46/0.71  thf('100', plain,
% 0.46/0.71      (((k1_relset_1 @ sk_B @ k1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.46/0.71         = (sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['98', '99'])).
% 0.46/0.71  thf('101', plain,
% 0.46/0.71      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)
% 0.46/0.71        | ((sk_B) != (sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['94', '97', '100'])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.46/0.71      inference('simplify', [status(thm)], ['101'])).
% 0.46/0.71  thf('103', plain, ($false), inference('demod', [status(thm)], ['89', '102'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
