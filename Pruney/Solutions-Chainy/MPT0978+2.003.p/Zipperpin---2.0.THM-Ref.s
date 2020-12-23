%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KWUcay6YmK

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 175 expanded)
%              Number of leaves         :   34 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  762 (3161 expanded)
%              Number of equality atoms :   32 (  96 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t24_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
             => ( ( k2_relset_1 @ A @ B @ C )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('43',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','32','41','42','43','44','47'])).

thf('49',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KWUcay6YmK
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 278 iterations in 0.184s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(t24_funct_2, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.63           ( ( r2_relset_1 @
% 0.46/0.63               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.46/0.63               ( k6_partfun1 @ B ) ) =>
% 0.46/0.63             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63          ( ![D:$i]:
% 0.46/0.63            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.63              ( ( r2_relset_1 @
% 0.46/0.63                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.46/0.63                  ( k6_partfun1 @ B ) ) =>
% 0.46/0.63                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k1_partfun1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( v1_funct_1 @ F ) & 
% 0.46/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.63       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.46/0.63          | ~ (v1_funct_1 @ X29)
% 0.46/0.63          | ~ (v1_funct_1 @ X32)
% 0.46/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.63          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.46/0.63              = (k5_relat_1 @ X29 @ X32)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.46/0.63            = (k5_relat_1 @ sk_D @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.46/0.63            = (k5_relat_1 @ sk_D @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.63          | ~ (v1_funct_1 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.46/0.63            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.63  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.46/0.63        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.46/0.63        (k6_partfun1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k1_partfun1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( v1_funct_1 @ F ) & 
% 0.46/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.63       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.63         ( m1_subset_1 @
% 0.46/0.63           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.46/0.63          | ~ (v1_funct_1 @ X23)
% 0.46/0.63          | ~ (v1_funct_1 @ X26)
% 0.46/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.63          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.63          | ~ (v1_funct_1 @ X1))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | (m1_subset_1 @ 
% 0.46/0.63           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '14'])).
% 0.46/0.63  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      ((m1_subset_1 @ 
% 0.46/0.63        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.63          | ((X18) = (X21))
% 0.46/0.63          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.46/0.63             (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ X0)
% 0.46/0.63          | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) = (X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_B) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.46/0.63        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.46/0.63            = (k6_partfun1 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '19'])).
% 0.46/0.63  thf(t29_relset_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( m1_subset_1 @
% 0.46/0.63       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X22 : $i]:
% 0.46/0.63         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.46/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.63  thf('22', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X22 : $i]:
% 0.46/0.63         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.46/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.46/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.46/0.63         = (k6_partfun1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '23'])).
% 0.46/0.63  thf('25', plain, (((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.46/0.63  thf(t45_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( v1_relat_1 @ B ) =>
% 0.46/0.63           ( r1_tarski @
% 0.46/0.63             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X5)
% 0.46/0.63          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.46/0.63             (k2_relat_1 @ X5))
% 0.46/0.63          | ~ (v1_relat_1 @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.46/0.63  thf(d10_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i, X2 : $i]:
% 0.46/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.46/0.63               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.46/0.63          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.63           (k2_relat_1 @ (k6_partfun1 @ sk_B)))
% 0.46/0.63        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '28'])).
% 0.46/0.63  thf(t71_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.63       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.63  thf('30', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.63  thf('31', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.63  thf('32', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.46/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((v5_relat_1 @ X12 @ X14)
% 0.46/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('35', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.63  thf(d19_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X3 : $i, X4 : $i]:
% 0.46/0.63         (~ (v5_relat_1 @ X3 @ X4)
% 0.46/0.63          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc1_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( v1_relat_1 @ C ) ))).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         ((v1_relat_1 @ X9)
% 0.46/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.63  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.63  thf('41', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '40'])).
% 0.46/0.63  thf('42', plain, (((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.46/0.63  thf('43', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.46/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         ((v1_relat_1 @ X9)
% 0.46/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.63  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.63  thf('48', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['29', '32', '41', '42', '43', '44', '47'])).
% 0.46/0.63  thf('49', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.63  thf('53', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['49', '52'])).
% 0.46/0.63  thf('54', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['48', '53'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
