%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bolaJgNOcK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:54 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 471 expanded)
%              Number of leaves         :   46 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          : 1035 (8748 expanded)
%              Number of equality atoms :   39 ( 102 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1 ) @ sk_B_1 @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) )
      | ~ ( v1_funct_1 @ X65 )
      | ( ( k2_partfun1 @ X66 @ X67 @ X65 @ X68 )
        = ( k7_relat_1 @ X65 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X62 @ X63 @ X61 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ sk_B_1 @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k7_relset_1 @ X44 @ X45 @ X43 @ X46 )
        = ( k9_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X62 @ X63 @ X61 @ X64 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X69 ) @ X70 )
      | ( v1_funct_2 @ X69 @ ( k1_relat_1 @ X69 ) @ X70 )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('51',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
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

thf('53',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ( X55
        = ( k1_relset_1 @ X55 @ X56 @ X57 ) )
      | ~ ( zip_tseitin_1 @ X57 @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
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

thf('60',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( zip_tseitin_0 @ X58 @ X59 )
      | ( zip_tseitin_1 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('64',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('65',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['61','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['58','73'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['27','28'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['51','78'])).

thf('80',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ sk_B_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['48','49','50','79'])).

thf('81',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['15','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('83',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X69 ) @ X70 )
      | ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X69 ) @ X70 ) ) )
      | ~ ( v1_funct_1 @ X69 )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('87',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['51','78'])).

thf('88',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['81','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bolaJgNOcK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.12/3.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.12/3.34  % Solved by: fo/fo7.sh
% 3.12/3.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.34  % done 3823 iterations in 2.882s
% 3.12/3.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.12/3.34  % SZS output start Refutation
% 3.12/3.34  thf(sk_B_type, type, sk_B: $i > $i).
% 3.12/3.34  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.12/3.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.12/3.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.12/3.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.12/3.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.12/3.34  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.12/3.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.12/3.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.12/3.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.12/3.34  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.34  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.12/3.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.12/3.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.12/3.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.12/3.34  thf(sk_D_type, type, sk_D: $i).
% 3.12/3.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.12/3.34  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.12/3.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.12/3.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.12/3.34  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.12/3.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.12/3.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.12/3.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.12/3.34  thf(sk_E_type, type, sk_E: $i).
% 3.12/3.34  thf(t178_funct_2, conjecture,
% 3.12/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.34     ( ( ~( v1_xboole_0 @ D ) ) =>
% 3.12/3.34       ( ![E:$i]:
% 3.12/3.34         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 3.12/3.34             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 3.12/3.34           ( ( ( r1_tarski @ B @ A ) & 
% 3.12/3.34               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 3.12/3.34             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 3.12/3.34               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 3.12/3.34               ( m1_subset_1 @
% 3.12/3.34                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 3.12/3.34                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.12/3.34  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.34        ( ( ~( v1_xboole_0 @ D ) ) =>
% 3.12/3.34          ( ![E:$i]:
% 3.12/3.34            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 3.12/3.34                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 3.12/3.34              ( ( ( r1_tarski @ B @ A ) & 
% 3.12/3.34                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 3.12/3.34                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 3.12/3.34                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 3.12/3.34                  ( m1_subset_1 @
% 3.12/3.34                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 3.12/3.34                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 3.12/3.34    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 3.12/3.34  thf('0', plain,
% 3.12/3.34      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1))
% 3.12/3.34        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1) @ 
% 3.12/3.34             sk_B_1 @ sk_C_1)
% 3.12/3.34        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B_1) @ 
% 3.12/3.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('1', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(redefinition_k2_partfun1, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.34     ( ( ( v1_funct_1 @ C ) & 
% 3.12/3.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.34       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 3.12/3.34  thf('2', plain,
% 3.12/3.34      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67)))
% 3.12/3.34          | ~ (v1_funct_1 @ X65)
% 3.12/3.34          | ((k2_partfun1 @ X66 @ X67 @ X65 @ X68) = (k7_relat_1 @ X65 @ X68)))),
% 3.12/3.34      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 3.12/3.34  thf('3', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 3.12/3.34          | ~ (v1_funct_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['1', '2'])).
% 3.12/3.34  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('5', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['3', '4'])).
% 3.12/3.34  thf('6', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(dt_k2_partfun1, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.34     ( ( ( v1_funct_1 @ C ) & 
% 3.12/3.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.12/3.34       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.12/3.34         ( m1_subset_1 @
% 3.12/3.34           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.12/3.34           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.12/3.34  thf('7', plain,
% 3.12/3.34      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 3.12/3.34          | ~ (v1_funct_1 @ X61)
% 3.12/3.34          | (v1_funct_1 @ (k2_partfun1 @ X62 @ X63 @ X61 @ X64)))),
% 3.12/3.34      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.12/3.34  thf('8', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 3.12/3.34          | ~ (v1_funct_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['6', '7'])).
% 3.12/3.34  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('10', plain,
% 3.12/3.34      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['8', '9'])).
% 3.12/3.34  thf('11', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['3', '4'])).
% 3.12/3.34  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['10', '11'])).
% 3.12/3.34  thf('13', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['3', '4'])).
% 3.12/3.34  thf('14', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['3', '4'])).
% 3.12/3.34  thf('15', plain,
% 3.12/3.34      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B_1) @ sk_B_1 @ sk_C_1)
% 3.12/3.34        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ 
% 3.12/3.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.34      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.12/3.34  thf('16', plain,
% 3.12/3.34      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B_1) @ sk_C_1)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('17', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(redefinition_k7_relset_1, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.34       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.12/3.34  thf('18', plain,
% 3.12/3.34      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 3.12/3.34          | ((k7_relset_1 @ X44 @ X45 @ X43 @ X46) = (k9_relat_1 @ X43 @ X46)))),
% 3.12/3.34      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.12/3.34  thf('19', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('sup-', [status(thm)], ['17', '18'])).
% 3.12/3.34  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B_1) @ sk_C_1)),
% 3.12/3.34      inference('demod', [status(thm)], ['16', '19'])).
% 3.12/3.34  thf(t148_relat_1, axiom,
% 3.12/3.34    (![A:$i,B:$i]:
% 3.12/3.34     ( ( v1_relat_1 @ B ) =>
% 3.12/3.34       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.12/3.34  thf('21', plain,
% 3.12/3.34      (![X23 : $i, X24 : $i]:
% 3.12/3.34         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 3.12/3.34          | ~ (v1_relat_1 @ X23))),
% 3.12/3.34      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.12/3.34  thf(d19_relat_1, axiom,
% 3.12/3.34    (![A:$i,B:$i]:
% 3.12/3.34     ( ( v1_relat_1 @ B ) =>
% 3.12/3.34       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.12/3.34  thf('22', plain,
% 3.12/3.34      (![X19 : $i, X20 : $i]:
% 3.12/3.34         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.12/3.34          | (v5_relat_1 @ X19 @ X20)
% 3.12/3.34          | ~ (v1_relat_1 @ X19))),
% 3.12/3.34      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.12/3.34  thf('23', plain,
% 3.12/3.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.34         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 3.12/3.34          | ~ (v1_relat_1 @ X1)
% 3.12/3.34          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.12/3.34          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 3.12/3.34      inference('sup-', [status(thm)], ['21', '22'])).
% 3.12/3.34  thf('24', plain,
% 3.12/3.34      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ sk_C_1)
% 3.12/3.34        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | ~ (v1_relat_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['20', '23'])).
% 3.12/3.34  thf('25', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(cc2_relat_1, axiom,
% 3.12/3.34    (![A:$i]:
% 3.12/3.34     ( ( v1_relat_1 @ A ) =>
% 3.12/3.34       ( ![B:$i]:
% 3.12/3.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.12/3.34  thf('26', plain,
% 3.12/3.34      (![X17 : $i, X18 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.12/3.34          | (v1_relat_1 @ X17)
% 3.12/3.34          | ~ (v1_relat_1 @ X18))),
% 3.12/3.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.12/3.34  thf('27', plain,
% 3.12/3.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['25', '26'])).
% 3.12/3.34  thf(fc6_relat_1, axiom,
% 3.12/3.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.12/3.34  thf('28', plain,
% 3.12/3.34      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.12/3.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.12/3.34  thf('29', plain, ((v1_relat_1 @ sk_E)),
% 3.12/3.34      inference('demod', [status(thm)], ['27', '28'])).
% 3.12/3.34  thf('30', plain,
% 3.12/3.34      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ sk_C_1)
% 3.12/3.34        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)))),
% 3.12/3.34      inference('demod', [status(thm)], ['24', '29'])).
% 3.12/3.34  thf('31', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('32', plain,
% 3.12/3.34      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 3.12/3.34          | ~ (v1_funct_1 @ X61)
% 3.12/3.34          | (m1_subset_1 @ (k2_partfun1 @ X62 @ X63 @ X61 @ X64) @ 
% 3.12/3.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 3.12/3.34      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.12/3.34  thf('33', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 3.12/3.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 3.12/3.34          | ~ (v1_funct_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['31', '32'])).
% 3.12/3.34  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('35', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 3.12/3.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('demod', [status(thm)], ['33', '34'])).
% 3.12/3.34  thf('36', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['3', '4'])).
% 3.12/3.34  thf('37', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 3.12/3.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('demod', [status(thm)], ['35', '36'])).
% 3.12/3.34  thf('38', plain,
% 3.12/3.34      (![X17 : $i, X18 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.12/3.34          | (v1_relat_1 @ X17)
% 3.12/3.34          | ~ (v1_relat_1 @ X18))),
% 3.12/3.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.12/3.34  thf('39', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 3.12/3.34          | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 3.12/3.34      inference('sup-', [status(thm)], ['37', '38'])).
% 3.12/3.34  thf('40', plain,
% 3.12/3.34      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.12/3.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.12/3.34  thf('41', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['39', '40'])).
% 3.12/3.34  thf('42', plain, ((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ sk_C_1)),
% 3.12/3.34      inference('demod', [status(thm)], ['30', '41'])).
% 3.12/3.34  thf('43', plain,
% 3.12/3.34      (![X19 : $i, X20 : $i]:
% 3.12/3.34         (~ (v5_relat_1 @ X19 @ X20)
% 3.12/3.34          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.12/3.34          | ~ (v1_relat_1 @ X19))),
% 3.12/3.34      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.12/3.34  thf('44', plain,
% 3.12/3.34      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) @ sk_C_1))),
% 3.12/3.34      inference('sup-', [status(thm)], ['42', '43'])).
% 3.12/3.34  thf('45', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['39', '40'])).
% 3.12/3.34  thf('46', plain,
% 3.12/3.34      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) @ sk_C_1)),
% 3.12/3.34      inference('demod', [status(thm)], ['44', '45'])).
% 3.12/3.34  thf(t4_funct_2, axiom,
% 3.12/3.34    (![A:$i,B:$i]:
% 3.12/3.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.12/3.34       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.12/3.34         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.12/3.34           ( m1_subset_1 @
% 3.12/3.34             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.12/3.34  thf('47', plain,
% 3.12/3.34      (![X69 : $i, X70 : $i]:
% 3.12/3.34         (~ (r1_tarski @ (k2_relat_1 @ X69) @ X70)
% 3.12/3.34          | (v1_funct_2 @ X69 @ (k1_relat_1 @ X69) @ X70)
% 3.12/3.34          | ~ (v1_funct_1 @ X69)
% 3.12/3.34          | ~ (v1_relat_1 @ X69))),
% 3.12/3.34      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.12/3.34  thf('48', plain,
% 3.12/3.34      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B_1) @ 
% 3.12/3.34           (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) @ sk_C_1))),
% 3.12/3.34      inference('sup-', [status(thm)], ['46', '47'])).
% 3.12/3.34  thf('49', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['39', '40'])).
% 3.12/3.34  thf('50', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['10', '11'])).
% 3.12/3.34  thf('51', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('52', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(d1_funct_2, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i]:
% 3.12/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.12/3.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.12/3.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.12/3.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.12/3.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.12/3.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.12/3.34  thf(zf_stmt_1, axiom,
% 3.12/3.34    (![C:$i,B:$i,A:$i]:
% 3.12/3.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.12/3.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.12/3.34  thf('53', plain,
% 3.12/3.34      (![X55 : $i, X56 : $i, X57 : $i]:
% 3.12/3.34         (~ (v1_funct_2 @ X57 @ X55 @ X56)
% 3.12/3.34          | ((X55) = (k1_relset_1 @ X55 @ X56 @ X57))
% 3.12/3.34          | ~ (zip_tseitin_1 @ X57 @ X56 @ X55))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.12/3.34  thf('54', plain,
% 3.12/3.34      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 3.12/3.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 3.12/3.34      inference('sup-', [status(thm)], ['52', '53'])).
% 3.12/3.34  thf('55', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(redefinition_k1_relset_1, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i]:
% 3.12/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.12/3.34  thf('56', plain,
% 3.12/3.34      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.12/3.34         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 3.12/3.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 3.12/3.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.12/3.34  thf('57', plain,
% 3.12/3.34      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.12/3.34      inference('sup-', [status(thm)], ['55', '56'])).
% 3.12/3.34  thf('58', plain,
% 3.12/3.34      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 3.12/3.34      inference('demod', [status(thm)], ['54', '57'])).
% 3.12/3.34  thf('59', plain,
% 3.12/3.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.12/3.34  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.12/3.34  thf(zf_stmt_4, axiom,
% 3.12/3.34    (![B:$i,A:$i]:
% 3.12/3.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.12/3.34       ( zip_tseitin_0 @ B @ A ) ))).
% 3.12/3.34  thf(zf_stmt_5, axiom,
% 3.12/3.34    (![A:$i,B:$i,C:$i]:
% 3.12/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.12/3.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.12/3.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.12/3.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.12/3.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.12/3.34  thf('60', plain,
% 3.12/3.34      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.12/3.34         (~ (zip_tseitin_0 @ X58 @ X59)
% 3.12/3.34          | (zip_tseitin_1 @ X60 @ X58 @ X59)
% 3.12/3.34          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.12/3.34  thf('61', plain,
% 3.12/3.34      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 3.12/3.34      inference('sup-', [status(thm)], ['59', '60'])).
% 3.12/3.34  thf('62', plain,
% 3.12/3.34      (![X53 : $i, X54 : $i]:
% 3.12/3.34         ((zip_tseitin_0 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.12/3.34  thf(rc2_subset_1, axiom,
% 3.12/3.34    (![A:$i]:
% 3.12/3.34     ( ?[B:$i]:
% 3.12/3.34       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 3.12/3.34  thf('63', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B @ X8))),
% 3.12/3.34      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.12/3.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.12/3.34  thf('64', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.12/3.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.12/3.34  thf(t3_subset, axiom,
% 3.12/3.34    (![A:$i,B:$i]:
% 3.12/3.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.12/3.34  thf('65', plain,
% 3.12/3.34      (![X11 : $i, X13 : $i]:
% 3.12/3.34         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 3.12/3.34      inference('cnf', [status(esa)], [t3_subset])).
% 3.12/3.34  thf('66', plain,
% 3.12/3.34      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.12/3.34      inference('sup-', [status(thm)], ['64', '65'])).
% 3.12/3.34  thf(cc1_subset_1, axiom,
% 3.12/3.34    (![A:$i]:
% 3.12/3.34     ( ( v1_xboole_0 @ A ) =>
% 3.12/3.34       ( ![B:$i]:
% 3.12/3.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.12/3.34  thf('67', plain,
% 3.12/3.34      (![X9 : $i, X10 : $i]:
% 3.12/3.34         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.12/3.34          | (v1_xboole_0 @ X9)
% 3.12/3.34          | ~ (v1_xboole_0 @ X10))),
% 3.12/3.34      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.12/3.34  thf('68', plain,
% 3.12/3.34      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 3.12/3.34      inference('sup-', [status(thm)], ['66', '67'])).
% 3.12/3.34  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.12/3.34      inference('sup-', [status(thm)], ['63', '68'])).
% 3.12/3.34  thf('70', plain,
% 3.12/3.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.12/3.34      inference('sup+', [status(thm)], ['62', '69'])).
% 3.12/3.34  thf('71', plain, (~ (v1_xboole_0 @ sk_D)),
% 3.12/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.34  thf('72', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_D @ X0)),
% 3.12/3.34      inference('sup-', [status(thm)], ['70', '71'])).
% 3.12/3.34  thf('73', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 3.12/3.34      inference('demod', [status(thm)], ['61', '72'])).
% 3.12/3.34  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 3.12/3.34      inference('demod', [status(thm)], ['58', '73'])).
% 3.12/3.34  thf(t91_relat_1, axiom,
% 3.12/3.34    (![A:$i,B:$i]:
% 3.12/3.34     ( ( v1_relat_1 @ B ) =>
% 3.12/3.34       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.12/3.34         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.12/3.34  thf('75', plain,
% 3.12/3.34      (![X29 : $i, X30 : $i]:
% 3.12/3.34         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 3.12/3.34          | ((k1_relat_1 @ (k7_relat_1 @ X30 @ X29)) = (X29))
% 3.12/3.34          | ~ (v1_relat_1 @ X30))),
% 3.12/3.34      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.12/3.34  thf('76', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (~ (r1_tarski @ X0 @ sk_A)
% 3.12/3.34          | ~ (v1_relat_1 @ sk_E)
% 3.12/3.34          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.12/3.34      inference('sup-', [status(thm)], ['74', '75'])).
% 3.12/3.34  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 3.12/3.34      inference('demod', [status(thm)], ['27', '28'])).
% 3.12/3.34  thf('78', plain,
% 3.12/3.34      (![X0 : $i]:
% 3.12/3.34         (~ (r1_tarski @ X0 @ sk_A)
% 3.12/3.34          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.12/3.34      inference('demod', [status(thm)], ['76', '77'])).
% 3.12/3.34  thf('79', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) = (sk_B_1))),
% 3.12/3.34      inference('sup-', [status(thm)], ['51', '78'])).
% 3.12/3.34  thf('80', plain,
% 3.12/3.34      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B_1) @ sk_B_1 @ sk_C_1)),
% 3.12/3.34      inference('demod', [status(thm)], ['48', '49', '50', '79'])).
% 3.12/3.34  thf('81', plain,
% 3.12/3.34      (~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ 
% 3.12/3.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.34      inference('demod', [status(thm)], ['15', '80'])).
% 3.12/3.34  thf('82', plain,
% 3.12/3.34      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) @ sk_C_1)),
% 3.12/3.34      inference('demod', [status(thm)], ['44', '45'])).
% 3.12/3.34  thf('83', plain,
% 3.12/3.34      (![X69 : $i, X70 : $i]:
% 3.12/3.34         (~ (r1_tarski @ (k2_relat_1 @ X69) @ X70)
% 3.12/3.34          | (m1_subset_1 @ X69 @ 
% 3.12/3.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X69) @ X70)))
% 3.12/3.34          | ~ (v1_funct_1 @ X69)
% 3.12/3.34          | ~ (v1_relat_1 @ X69))),
% 3.12/3.34      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.12/3.34  thf('84', plain,
% 3.12/3.34      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B_1))
% 3.12/3.34        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ 
% 3.12/3.34           (k1_zfmisc_1 @ 
% 3.12/3.34            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) @ sk_C_1))))),
% 3.12/3.34      inference('sup-', [status(thm)], ['82', '83'])).
% 3.12/3.34  thf('85', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['39', '40'])).
% 3.12/3.34  thf('86', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.12/3.34      inference('demod', [status(thm)], ['10', '11'])).
% 3.12/3.34  thf('87', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B_1)) = (sk_B_1))),
% 3.12/3.34      inference('sup-', [status(thm)], ['51', '78'])).
% 3.12/3.34  thf('88', plain,
% 3.12/3.34      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B_1) @ 
% 3.12/3.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.34      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 3.12/3.34  thf('89', plain, ($false), inference('demod', [status(thm)], ['81', '88'])).
% 3.12/3.34  
% 3.12/3.34  % SZS output end Refutation
% 3.12/3.34  
% 3.12/3.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
