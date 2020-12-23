%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2BC1Kauf4

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 220 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  822 (4180 expanded)
%              Number of equality atoms :   33 ( 125 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['34','35','44','45','46','51','56'])).

thf('58',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2BC1Kauf4
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.77  % Solved by: fo/fo7.sh
% 0.52/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.77  % done 570 iterations in 0.317s
% 0.52/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.77  % SZS output start Refutation
% 0.52/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.77  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.52/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.77  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.52/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.77  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.52/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.77  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.77  thf(t24_funct_2, conjecture,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.77       ( ![D:$i]:
% 0.52/0.77         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.52/0.77             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.52/0.77           ( ( r2_relset_1 @
% 0.52/0.77               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.52/0.77               ( k6_partfun1 @ B ) ) =>
% 0.52/0.77             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.52/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.77          ( ![D:$i]:
% 0.52/0.77            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.52/0.77                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.52/0.77              ( ( r2_relset_1 @
% 0.52/0.77                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.52/0.77                  ( k6_partfun1 @ B ) ) =>
% 0.52/0.77                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.52/0.77    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.52/0.77  thf('0', plain,
% 0.52/0.77      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.52/0.77        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.52/0.77        (k6_partfun1 @ sk_B))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(redefinition_k6_partfun1, axiom,
% 0.52/0.77    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.52/0.77  thf('1', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.77  thf('2', plain,
% 0.52/0.77      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.52/0.77        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.52/0.77        (k6_relat_1 @ sk_B))),
% 0.52/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.77  thf('3', plain,
% 0.52/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('4', plain,
% 0.52/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(redefinition_k1_partfun1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.77     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.77         ( v1_funct_1 @ F ) & 
% 0.52/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.52/0.77       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.52/0.77  thf('5', plain,
% 0.52/0.77      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.52/0.77          | ~ (v1_funct_1 @ X32)
% 0.52/0.77          | ~ (v1_funct_1 @ X35)
% 0.52/0.77          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.52/0.77          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.52/0.77              = (k5_relat_1 @ X32 @ X35)))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.52/0.77  thf('6', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.52/0.77            = (k5_relat_1 @ sk_D @ X0))
% 0.52/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.77          | ~ (v1_funct_1 @ X0)
% 0.52/0.77          | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.77  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('8', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.52/0.77            = (k5_relat_1 @ sk_D @ X0))
% 0.52/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.77          | ~ (v1_funct_1 @ X0))),
% 0.52/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.77  thf('9', plain,
% 0.52/0.77      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.77        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.52/0.77            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['3', '8'])).
% 0.52/0.77  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('11', plain,
% 0.52/0.77      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.52/0.77         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.52/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.77  thf('12', plain,
% 0.52/0.77      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.52/0.77        (k6_relat_1 @ sk_B))),
% 0.52/0.77      inference('demod', [status(thm)], ['2', '11'])).
% 0.52/0.77  thf('13', plain,
% 0.52/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('14', plain,
% 0.52/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(dt_k1_partfun1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.77     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.77         ( v1_funct_1 @ F ) & 
% 0.52/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.52/0.77       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.52/0.77         ( m1_subset_1 @
% 0.52/0.77           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.52/0.77  thf('15', plain,
% 0.52/0.77      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.52/0.77          | ~ (v1_funct_1 @ X24)
% 0.52/0.77          | ~ (v1_funct_1 @ X27)
% 0.52/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.52/0.77          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.52/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.52/0.77      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.52/0.77  thf('16', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.52/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.52/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.52/0.77          | ~ (v1_funct_1 @ X1)
% 0.52/0.77          | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.77  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('18', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.52/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.52/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.52/0.77          | ~ (v1_funct_1 @ X1))),
% 0.52/0.77      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.77  thf('19', plain,
% 0.52/0.77      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.77        | (m1_subset_1 @ 
% 0.52/0.77           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.52/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['13', '18'])).
% 0.52/0.77  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('21', plain,
% 0.52/0.77      ((m1_subset_1 @ 
% 0.52/0.77        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.52/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.52/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.77  thf('22', plain,
% 0.52/0.77      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.52/0.77         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.52/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.77  thf('23', plain,
% 0.52/0.77      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.52/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.52/0.77      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.77  thf(redefinition_r2_relset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.77     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.77       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.52/0.77  thf('24', plain,
% 0.52/0.77      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.52/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.52/0.77          | ((X20) = (X23))
% 0.52/0.77          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.52/0.77  thf('25', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.60/0.77          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.77  thf('26', plain,
% 0.60/0.77      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.60/0.77        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['12', '25'])).
% 0.60/0.77  thf(dt_k6_partfun1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( m1_subset_1 @
% 0.60/0.77         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.60/0.77       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.60/0.77  thf('27', plain,
% 0.60/0.77      (![X31 : $i]:
% 0.60/0.77         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.60/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.60/0.77  thf('28', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.60/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (![X31 : $i]:
% 0.60/0.77         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.60/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.60/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.60/0.77  thf('30', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.60/0.77      inference('demod', [status(thm)], ['26', '29'])).
% 0.60/0.77  thf(t45_relat_1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( v1_relat_1 @ A ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( v1_relat_1 @ B ) =>
% 0.60/0.77           ( r1_tarski @
% 0.60/0.77             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.60/0.77  thf('31', plain,
% 0.60/0.77      (![X10 : $i, X11 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X10)
% 0.60/0.77          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.60/0.77             (k2_relat_1 @ X10))
% 0.60/0.77          | ~ (v1_relat_1 @ X11))),
% 0.60/0.77      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.60/0.77  thf(d10_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.77  thf('32', plain,
% 0.60/0.77      (![X0 : $i, X2 : $i]:
% 0.60/0.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.77  thf('33', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X1)
% 0.60/0.77          | ~ (v1_relat_1 @ X0)
% 0.60/0.77          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.60/0.77               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.60/0.77          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.77  thf('34', plain,
% 0.60/0.77      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.60/0.77        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.60/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.60/0.77        | ~ (v1_relat_1 @ sk_D))),
% 0.60/0.77      inference('sup-', [status(thm)], ['30', '33'])).
% 0.60/0.77  thf(t71_relat_1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.60/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.60/0.77  thf('35', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.77  thf('36', plain,
% 0.60/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(dt_k2_relset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.77       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.60/0.77  thf('37', plain,
% 0.60/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.77         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.60/0.77          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.60/0.77  thf('38', plain,
% 0.60/0.77      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.77  thf('39', plain,
% 0.60/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.77  thf('40', plain,
% 0.60/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.77         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.60/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.60/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.77  thf('41', plain,
% 0.60/0.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.60/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.77  thf('42', plain,
% 0.60/0.77      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.60/0.77      inference('demod', [status(thm)], ['38', '41'])).
% 0.60/0.77  thf(t3_subset, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.77  thf('43', plain,
% 0.60/0.77      (![X3 : $i, X4 : $i]:
% 0.60/0.77         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.77  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.60/0.77      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.77  thf('45', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.60/0.77      inference('demod', [status(thm)], ['26', '29'])).
% 0.60/0.77  thf('46', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.77  thf('47', plain,
% 0.60/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(cc2_relat_1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( v1_relat_1 @ A ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.77  thf('48', plain,
% 0.60/0.77      (![X6 : $i, X7 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.60/0.77          | (v1_relat_1 @ X6)
% 0.60/0.77          | ~ (v1_relat_1 @ X7))),
% 0.60/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.77  thf('49', plain,
% 0.60/0.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.60/0.77      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.77  thf(fc6_relat_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.77  thf('50', plain,
% 0.60/0.77      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.60/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.77  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.77  thf('52', plain,
% 0.60/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('53', plain,
% 0.60/0.77      (![X6 : $i, X7 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.60/0.77          | (v1_relat_1 @ X6)
% 0.60/0.77          | ~ (v1_relat_1 @ X7))),
% 0.60/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.77  thf('54', plain,
% 0.60/0.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.60/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.60/0.77  thf('55', plain,
% 0.60/0.77      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.60/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.77  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.77      inference('demod', [status(thm)], ['54', '55'])).
% 0.60/0.77  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.60/0.77      inference('demod', [status(thm)],
% 0.60/0.77                ['34', '35', '44', '45', '46', '51', '56'])).
% 0.60/0.77  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('59', plain,
% 0.60/0.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.60/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.77  thf('60', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.60/0.77      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.77  thf('61', plain, ($false),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['57', '60'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
