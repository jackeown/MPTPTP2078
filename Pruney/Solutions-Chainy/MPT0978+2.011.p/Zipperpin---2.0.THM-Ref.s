%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Aga40p2Liy

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 275 expanded)
%              Number of leaves         :   37 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  956 (4996 expanded)
%              Number of equality atoms :   38 ( 145 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) )
    | ( v1_relat_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    v1_relat_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','23','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ X0 )
      | ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('51',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('54',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('58',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['35','57','60','67','68','69'])).

thf('71',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Aga40p2Liy
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.81  % Solved by: fo/fo7.sh
% 0.63/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.81  % done 534 iterations in 0.353s
% 0.63/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.81  % SZS output start Refutation
% 0.63/0.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.63/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.63/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.63/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.63/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.63/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.63/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.63/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.63/0.81  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.63/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.63/0.81  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.63/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.63/0.81  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.63/0.81  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.63/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.63/0.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.63/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.63/0.81  thf(t24_funct_2, conjecture,
% 0.63/0.81    (![A:$i,B:$i,C:$i]:
% 0.63/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.81       ( ![D:$i]:
% 0.63/0.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.63/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.63/0.81           ( ( r2_relset_1 @
% 0.63/0.81               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.63/0.81               ( k6_partfun1 @ B ) ) =>
% 0.63/0.81             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.63/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.63/0.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.81            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.81          ( ![D:$i]:
% 0.63/0.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.63/0.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.63/0.81              ( ( r2_relset_1 @
% 0.63/0.81                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.63/0.81                  ( k6_partfun1 @ B ) ) =>
% 0.63/0.81                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.63/0.81    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.63/0.81  thf('0', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('1', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(dt_k4_relset_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.81     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.63/0.81       ( m1_subset_1 @
% 0.63/0.81         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.63/0.81         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.63/0.81  thf('2', plain,
% 0.63/0.81      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.63/0.81          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.63/0.81          | (m1_subset_1 @ (k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.63/0.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.63/0.81      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.63/0.81  thf('3', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         ((m1_subset_1 @ (k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.63/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.63/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.63/0.81  thf('4', plain,
% 0.63/0.81      ((m1_subset_1 @ 
% 0.63/0.81        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.63/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['0', '3'])).
% 0.63/0.81  thf(cc2_relat_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( v1_relat_1 @ A ) =>
% 0.63/0.81       ( ![B:$i]:
% 0.63/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.63/0.81  thf('5', plain,
% 0.63/0.81      (![X3 : $i, X4 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.63/0.81          | (v1_relat_1 @ X3)
% 0.63/0.81          | ~ (v1_relat_1 @ X4))),
% 0.63/0.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.63/0.81  thf('6', plain,
% 0.63/0.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))
% 0.63/0.81        | (v1_relat_1 @ (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.63/0.81  thf(fc6_relat_1, axiom,
% 0.63/0.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.63/0.81  thf('7', plain,
% 0.63/0.81      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.63/0.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.63/0.81  thf('8', plain,
% 0.63/0.81      ((v1_relat_1 @ (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['6', '7'])).
% 0.63/0.81  thf('9', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('10', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(redefinition_k4_relset_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.81     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.63/0.81       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.63/0.81  thf('11', plain,
% 0.63/0.81      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.63/0.81          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.63/0.81          | ((k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.63/0.81              = (k5_relat_1 @ X25 @ X28)))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.63/0.81  thf('12', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (((k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.63/0.81            = (k5_relat_1 @ sk_D @ X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.63/0.81  thf('13', plain,
% 0.63/0.81      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.63/0.81         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['9', '12'])).
% 0.63/0.81  thf('14', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['8', '13'])).
% 0.63/0.81  thf(t45_relat_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( v1_relat_1 @ A ) =>
% 0.63/0.81       ( ![B:$i]:
% 0.63/0.81         ( ( v1_relat_1 @ B ) =>
% 0.63/0.81           ( r1_tarski @
% 0.63/0.81             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.63/0.81  thf('15', plain,
% 0.63/0.81      (![X9 : $i, X10 : $i]:
% 0.63/0.81         (~ (v1_relat_1 @ X9)
% 0.63/0.81          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.63/0.81             (k2_relat_1 @ X9))
% 0.63/0.81          | ~ (v1_relat_1 @ X10))),
% 0.63/0.81      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.63/0.81  thf(d19_relat_1, axiom,
% 0.63/0.81    (![A:$i,B:$i]:
% 0.63/0.81     ( ( v1_relat_1 @ B ) =>
% 0.63/0.81       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.63/0.81  thf('16', plain,
% 0.63/0.81      (![X5 : $i, X6 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.63/0.81          | (v5_relat_1 @ X5 @ X6)
% 0.63/0.81          | ~ (v1_relat_1 @ X5))),
% 0.63/0.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.63/0.81  thf('17', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         (~ (v1_relat_1 @ X1)
% 0.63/0.81          | ~ (v1_relat_1 @ X0)
% 0.63/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.63/0.81          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.63/0.81  thf('18', plain,
% 0.63/0.81      (((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.63/0.81        | ~ (v1_relat_1 @ sk_C)
% 0.63/0.81        | ~ (v1_relat_1 @ sk_D))),
% 0.63/0.81      inference('sup-', [status(thm)], ['14', '17'])).
% 0.63/0.81  thf('19', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('20', plain,
% 0.63/0.81      (![X3 : $i, X4 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.63/0.81          | (v1_relat_1 @ X3)
% 0.63/0.81          | ~ (v1_relat_1 @ X4))),
% 0.63/0.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.63/0.81  thf('21', plain,
% 0.63/0.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.63/0.81  thf('22', plain,
% 0.63/0.81      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.63/0.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.63/0.81  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '22'])).
% 0.63/0.81  thf('24', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('25', plain,
% 0.63/0.81      (![X3 : $i, X4 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.63/0.81          | (v1_relat_1 @ X3)
% 0.63/0.81          | ~ (v1_relat_1 @ X4))),
% 0.63/0.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.63/0.81  thf('26', plain,
% 0.63/0.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.63/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.63/0.81  thf('27', plain,
% 0.63/0.81      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.63/0.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.63/0.81  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.63/0.81      inference('demod', [status(thm)], ['26', '27'])).
% 0.63/0.81  thf('29', plain,
% 0.63/0.81      ((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['18', '23', '28'])).
% 0.63/0.81  thf('30', plain,
% 0.63/0.81      (![X5 : $i, X6 : $i]:
% 0.63/0.81         (~ (v5_relat_1 @ X5 @ X6)
% 0.63/0.81          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.63/0.81          | ~ (v1_relat_1 @ X5))),
% 0.63/0.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.63/0.81  thf('31', plain,
% 0.63/0.81      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))
% 0.63/0.81        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.63/0.81           (k2_relat_1 @ sk_C)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.63/0.81  thf('32', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['8', '13'])).
% 0.63/0.81  thf('33', plain,
% 0.63/0.81      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)) @ 
% 0.63/0.81        (k2_relat_1 @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['31', '32'])).
% 0.63/0.81  thf(d10_xboole_0, axiom,
% 0.63/0.81    (![A:$i,B:$i]:
% 0.63/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.63/0.81  thf('34', plain,
% 0.63/0.81      (![X0 : $i, X2 : $i]:
% 0.63/0.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.63/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.81  thf('35', plain,
% 0.63/0.81      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.63/0.81           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.63/0.81        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.63/0.81  thf('36', plain,
% 0.63/0.81      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.63/0.81        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.63/0.81        (k6_partfun1 @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('37', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('38', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(redefinition_k1_partfun1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.81     ( ( ( v1_funct_1 @ E ) & 
% 0.63/0.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.81         ( v1_funct_1 @ F ) & 
% 0.63/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.63/0.81       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.63/0.81  thf('39', plain,
% 0.63/0.81      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.63/0.81          | ~ (v1_funct_1 @ X36)
% 0.63/0.81          | ~ (v1_funct_1 @ X39)
% 0.63/0.81          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.63/0.81          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.63/0.81              = (k5_relat_1 @ X36 @ X39)))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.63/0.81  thf('40', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.63/0.81            = (k5_relat_1 @ sk_D @ X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.81          | ~ (v1_funct_1 @ X0)
% 0.63/0.81          | ~ (v1_funct_1 @ sk_D))),
% 0.63/0.81      inference('sup-', [status(thm)], ['38', '39'])).
% 0.63/0.81  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('42', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.63/0.81            = (k5_relat_1 @ sk_D @ X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.81          | ~ (v1_funct_1 @ X0))),
% 0.63/0.81      inference('demod', [status(thm)], ['40', '41'])).
% 0.63/0.81  thf('43', plain,
% 0.63/0.81      ((~ (v1_funct_1 @ sk_C)
% 0.63/0.81        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.63/0.81            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['37', '42'])).
% 0.63/0.81  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('45', plain,
% 0.63/0.81      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.63/0.81         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['43', '44'])).
% 0.63/0.81  thf('46', plain,
% 0.63/0.81      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.63/0.81        (k6_partfun1 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['36', '45'])).
% 0.63/0.81  thf('47', plain,
% 0.63/0.81      ((m1_subset_1 @ 
% 0.63/0.81        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.63/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['0', '3'])).
% 0.63/0.81  thf(redefinition_r2_relset_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.81     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.81       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.63/0.81  thf('48', plain,
% 0.63/0.81      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.63/0.81          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.63/0.81          | ((X31) = (X34))
% 0.63/0.81          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.63/0.81  thf('49', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.63/0.81             (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ X0)
% 0.63/0.81          | ((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) = (X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.63/0.81  thf('50', plain,
% 0.63/0.81      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.63/0.81         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['9', '12'])).
% 0.63/0.81  thf('51', plain,
% 0.63/0.81      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.63/0.81         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['9', '12'])).
% 0.63/0.81  thf('52', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.63/0.81          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.63/0.81      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.63/0.81  thf('53', plain,
% 0.63/0.81      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_B) @ 
% 0.63/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.63/0.81        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['46', '52'])).
% 0.63/0.81  thf(t29_relset_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( m1_subset_1 @
% 0.63/0.81       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.63/0.81  thf('54', plain,
% 0.63/0.81      (![X35 : $i]:
% 0.63/0.81         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.63/0.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.63/0.81      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.63/0.81  thf(redefinition_k6_partfun1, axiom,
% 0.63/0.81    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.63/0.81  thf('55', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.81  thf('56', plain,
% 0.63/0.81      (![X35 : $i]:
% 0.63/0.81         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.63/0.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.63/0.81      inference('demod', [status(thm)], ['54', '55'])).
% 0.63/0.81  thf('57', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['53', '56'])).
% 0.63/0.81  thf(t71_relat_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.63/0.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.63/0.81  thf('58', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.63/0.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.63/0.81  thf('59', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.81  thf('60', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 0.63/0.81      inference('demod', [status(thm)], ['58', '59'])).
% 0.63/0.81  thf('61', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(cc2_relset_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i]:
% 0.63/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.63/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.63/0.81  thf('62', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((v5_relat_1 @ X13 @ X15)
% 0.63/0.81          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.63/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.63/0.81  thf('63', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.63/0.81      inference('sup-', [status(thm)], ['61', '62'])).
% 0.63/0.81  thf('64', plain,
% 0.63/0.81      (![X5 : $i, X6 : $i]:
% 0.63/0.81         (~ (v5_relat_1 @ X5 @ X6)
% 0.63/0.81          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.63/0.81          | ~ (v1_relat_1 @ X5))),
% 0.63/0.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.63/0.81  thf('65', plain,
% 0.63/0.81      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.63/0.81      inference('sup-', [status(thm)], ['63', '64'])).
% 0.63/0.81  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '22'])).
% 0.63/0.81  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.63/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.63/0.81  thf('68', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['53', '56'])).
% 0.63/0.81  thf('69', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 0.63/0.81      inference('demod', [status(thm)], ['58', '59'])).
% 0.63/0.81  thf('70', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['35', '57', '60', '67', '68', '69'])).
% 0.63/0.81  thf('71', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('72', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(redefinition_k2_relset_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i]:
% 0.63/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.63/0.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.63/0.81  thf('73', plain,
% 0.63/0.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.63/0.81         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.63/0.81          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.63/0.81  thf('74', plain,
% 0.63/0.81      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.63/0.81  thf('75', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['71', '74'])).
% 0.63/0.81  thf('76', plain, ($false),
% 0.63/0.81      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.63/0.81  
% 0.63/0.81  % SZS output end Refutation
% 0.63/0.81  
% 0.63/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
