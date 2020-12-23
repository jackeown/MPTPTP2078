%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TNyuBtqPOk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:51 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 261 expanded)
%              Number of leaves         :   37 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  927 (4936 expanded)
%              Number of equality atoms :   37 ( 143 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('6',plain,(
    v1_relat_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ X0 )
      | ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('47',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('50',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('51',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('54',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('63',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','53','54','61','62','63'])).

thf('65',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TNyuBtqPOk
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 535 iterations in 0.283s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.56/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.56/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.56/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.56/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.56/0.74  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.56/0.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.56/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.56/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.56/0.74  thf(t24_funct_2, conjecture,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.74       ( ![D:$i]:
% 0.56/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.56/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.56/0.74           ( ( r2_relset_1 @
% 0.56/0.74               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.56/0.74               ( k6_partfun1 @ B ) ) =>
% 0.56/0.74             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.74          ( ![D:$i]:
% 0.56/0.74            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.56/0.74                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.56/0.74              ( ( r2_relset_1 @
% 0.56/0.74                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.56/0.74                  ( k6_partfun1 @ B ) ) =>
% 0.56/0.74                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.56/0.74  thf('0', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(dt_k4_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.56/0.74     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.56/0.74       ( m1_subset_1 @
% 0.56/0.74         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.56/0.74         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.56/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.56/0.74          | (m1_subset_1 @ (k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 0.56/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((m1_subset_1 @ (k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.56/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.56/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf('4', plain,
% 0.56/0.74      ((m1_subset_1 @ 
% 0.56/0.74        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.56/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['0', '3'])).
% 0.56/0.74  thf(cc1_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.74       ( v1_relat_1 @ C ) ))).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.56/0.74         ((v1_relat_1 @ X9)
% 0.56/0.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      ((v1_relat_1 @ (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('8', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(redefinition_k4_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.56/0.74     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.56/0.74       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.56/0.74          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.56/0.74          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.56/0.74              = (k5_relat_1 @ X24 @ X27)))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (((k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.56/0.74            = (k5_relat_1 @ sk_D @ X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.74  thf('11', plain,
% 0.56/0.74      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.56/0.74         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.74  thf('12', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['6', '11'])).
% 0.56/0.74  thf(t45_relat_1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ A ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( v1_relat_1 @ B ) =>
% 0.56/0.74           ( r1_tarski @
% 0.56/0.74             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.56/0.74  thf('13', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X5)
% 0.56/0.74          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.56/0.74             (k2_relat_1 @ X5))
% 0.56/0.74          | ~ (v1_relat_1 @ X6))),
% 0.56/0.74      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.56/0.74  thf(d19_relat_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( v1_relat_1 @ B ) =>
% 0.56/0.74       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X3 : $i, X4 : $i]:
% 0.56/0.74         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.56/0.74          | (v5_relat_1 @ X3 @ X4)
% 0.56/0.74          | ~ (v1_relat_1 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.56/0.74  thf('15', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v1_relat_1 @ X1)
% 0.56/0.74          | ~ (v1_relat_1 @ X0)
% 0.56/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.56/0.74          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.56/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.56/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.56/0.74      inference('sup-', [status(thm)], ['12', '15'])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('18', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.56/0.74         ((v1_relat_1 @ X9)
% 0.56/0.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.74  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.56/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.56/0.74         ((v1_relat_1 @ X9)
% 0.56/0.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.74  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      ((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      (![X3 : $i, X4 : $i]:
% 0.56/0.74         (~ (v5_relat_1 @ X3 @ X4)
% 0.56/0.74          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.56/0.74          | ~ (v1_relat_1 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))
% 0.56/0.74        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.56/0.74           (k2_relat_1 @ sk_C)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.74  thf('26', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['6', '11'])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.56/0.74        (k2_relat_1 @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.74  thf(d10_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.74  thf('28', plain,
% 0.56/0.74      (![X0 : $i, X2 : $i]:
% 0.56/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.56/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.74  thf('29', plain,
% 0.56/0.74      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.56/0.74           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.56/0.74        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.56/0.74        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.56/0.74        (k6_partfun1 @ sk_B))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(redefinition_k6_partfun1, axiom,
% 0.56/0.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.56/0.74  thf('31', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.56/0.74  thf('32', plain,
% 0.56/0.74      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.56/0.74        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.56/0.74        (k6_relat_1 @ sk_B))),
% 0.56/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('34', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(redefinition_k1_partfun1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.56/0.74     ( ( ( v1_funct_1 @ E ) & 
% 0.56/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.74         ( v1_funct_1 @ F ) & 
% 0.56/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.56/0.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.56/0.74          | ~ (v1_funct_1 @ X36)
% 0.56/0.74          | ~ (v1_funct_1 @ X39)
% 0.56/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.56/0.74          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.56/0.74              = (k5_relat_1 @ X36 @ X39)))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.56/0.74            = (k5_relat_1 @ sk_D @ X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.56/0.74          | ~ (v1_funct_1 @ X0)
% 0.56/0.74          | ~ (v1_funct_1 @ sk_D))),
% 0.56/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.56/0.74  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.56/0.74            = (k5_relat_1 @ sk_D @ X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.56/0.74          | ~ (v1_funct_1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.74  thf('39', plain,
% 0.56/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.56/0.74        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.56/0.74            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['33', '38'])).
% 0.56/0.74  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.56/0.74         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.56/0.74  thf('42', plain,
% 0.56/0.74      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.56/0.74        (k6_relat_1 @ sk_B))),
% 0.56/0.74      inference('demod', [status(thm)], ['32', '41'])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      ((m1_subset_1 @ 
% 0.56/0.74        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.56/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['0', '3'])).
% 0.56/0.74  thf(redefinition_r2_relset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.56/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.56/0.74          | ((X30) = (X33))
% 0.56/0.74          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.56/0.74             (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ X0)
% 0.56/0.74          | ((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) = (X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.56/0.74         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.74  thf('47', plain,
% 0.56/0.74      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.56/0.74         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.56/0.74      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.74  thf('48', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.56/0.74          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.56/0.74      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.56/0.74  thf('49', plain,
% 0.56/0.74      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.56/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.56/0.74        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['42', '48'])).
% 0.56/0.74  thf(dt_k6_partfun1, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( m1_subset_1 @
% 0.56/0.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.56/0.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.56/0.74  thf('50', plain,
% 0.56/0.74      (![X35 : $i]:
% 0.56/0.74         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.56/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.56/0.75      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.56/0.75  thf('51', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.56/0.75  thf('52', plain,
% 0.56/0.75      (![X35 : $i]:
% 0.56/0.75         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.56/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.56/0.75      inference('demod', [status(thm)], ['50', '51'])).
% 0.56/0.75  thf('53', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['49', '52'])).
% 0.56/0.75  thf(t71_relat_1, axiom,
% 0.56/0.75    (![A:$i]:
% 0.56/0.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.56/0.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.56/0.75  thf('54', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.56/0.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.56/0.75  thf('55', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(cc2_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.75  thf('56', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.56/0.75         ((v5_relat_1 @ X12 @ X14)
% 0.56/0.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.75  thf('57', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.56/0.75      inference('sup-', [status(thm)], ['55', '56'])).
% 0.56/0.75  thf('58', plain,
% 0.56/0.75      (![X3 : $i, X4 : $i]:
% 0.56/0.75         (~ (v5_relat_1 @ X3 @ X4)
% 0.56/0.75          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.56/0.75          | ~ (v1_relat_1 @ X3))),
% 0.56/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.56/0.75  thf('59', plain,
% 0.56/0.75      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.56/0.75      inference('sup-', [status(thm)], ['57', '58'])).
% 0.56/0.75  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.56/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.75  thf('61', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.56/0.75      inference('demod', [status(thm)], ['59', '60'])).
% 0.56/0.75  thf('62', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['49', '52'])).
% 0.56/0.75  thf('63', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.56/0.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.56/0.75  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['29', '53', '54', '61', '62', '63'])).
% 0.56/0.75  thf('65', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('66', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.56/0.75  thf('67', plain,
% 0.56/0.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.56/0.75         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.56/0.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.56/0.75  thf('68', plain,
% 0.56/0.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.56/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.56/0.75  thf('69', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.56/0.75      inference('demod', [status(thm)], ['65', '68'])).
% 0.56/0.75  thf('70', plain, ($false),
% 0.56/0.75      inference('simplify_reflect-', [status(thm)], ['64', '69'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
