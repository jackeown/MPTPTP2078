%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z7bmrknmxe

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:54 EST 2020

% Result     : Theorem 3.69s
% Output     : Refutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  212 (4017 expanded)
%              Number of leaves         :   51 (1203 expanded)
%              Depth                    :   22
%              Number of atoms          : 1580 (74009 expanded)
%              Number of equality atoms :   89 (1131 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ( ( k2_partfun1 @ X58 @ X59 @ X57 @ X60 )
        = ( k7_relat_1 @ X57 @ X60 ) ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X54 @ X55 @ X53 @ X56 ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k9_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k9_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X54 @ X55 @ X53 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['24','35','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X42 ) @ X43 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X44 )
      | ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ( X47
        = ( k1_relset_1 @ X47 @ X48 @ X49 ) )
      | ~ ( zip_tseitin_1 @ X49 @ X48 @ X47 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
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

thf('63',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X50 @ X51 )
      | ( zip_tseitin_1 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['58','67'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['51','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('75',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','73','74'])).

thf('76',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','75'])).

thf('77',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','73','74'])).

thf('79',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X50 @ X51 )
      | ( zip_tseitin_1 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','73','74'])).

thf('83',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['51','72'])).

thf('86',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47
       != ( k1_relset_1 @ X47 @ X48 @ X49 ) )
      | ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ~ ( zip_tseitin_1 @ X49 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','75'])).

thf('91',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['51','72'])).

thf('95',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','73','74'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','91'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('103',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('104',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','91'])).

thf('105',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','102','103','104','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['94','106'])).

thf('108',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('109',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('111',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('112',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('113',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('116',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('118',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['114','118'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('120',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('121',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','121'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('123',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('124',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('126',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ) @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) )
      = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('136',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('137',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('138',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('139',plain,
    ( ( k1_xboole_0
      = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( k1_xboole_0
      = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf('142',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','121'])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('145',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47
       != ( k1_relset_1 @ X47 @ X48 @ X49 ) )
      | ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ~ ( zip_tseitin_1 @ X49 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( X46 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('153',plain,(
    ! [X45: $i] :
      ( zip_tseitin_0 @ X45 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('155',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X50 @ X51 )
      | ( zip_tseitin_1 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['151','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['93','122','142','143','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z7bmrknmxe
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.69/3.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.69/3.89  % Solved by: fo/fo7.sh
% 3.69/3.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.69/3.89  % done 5115 iterations in 3.437s
% 3.69/3.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.69/3.89  % SZS output start Refutation
% 3.69/3.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.69/3.89  thf(sk_E_type, type, sk_E: $i).
% 3.69/3.89  thf(sk_D_type, type, sk_D: $i).
% 3.69/3.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.69/3.89  thf(sk_C_type, type, sk_C: $i).
% 3.69/3.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.69/3.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.69/3.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.69/3.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.69/3.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.69/3.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.69/3.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.69/3.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.69/3.89  thf(sk_A_type, type, sk_A: $i).
% 3.69/3.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.69/3.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.69/3.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.69/3.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.69/3.89  thf(sk_B_type, type, sk_B: $i).
% 3.69/3.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.69/3.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.69/3.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.69/3.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.69/3.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.69/3.89  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.69/3.89  thf(t178_funct_2, conjecture,
% 3.69/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.69/3.89     ( ( ~( v1_xboole_0 @ D ) ) =>
% 3.69/3.89       ( ![E:$i]:
% 3.69/3.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 3.69/3.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 3.69/3.89           ( ( ( r1_tarski @ B @ A ) & 
% 3.69/3.89               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 3.69/3.89             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 3.69/3.89               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 3.69/3.89               ( m1_subset_1 @
% 3.69/3.89                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 3.69/3.89                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.69/3.89  thf(zf_stmt_0, negated_conjecture,
% 3.69/3.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.69/3.89        ( ( ~( v1_xboole_0 @ D ) ) =>
% 3.69/3.89          ( ![E:$i]:
% 3.69/3.89            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 3.69/3.89                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 3.69/3.89              ( ( ( r1_tarski @ B @ A ) & 
% 3.69/3.89                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 3.69/3.89                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 3.69/3.89                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 3.69/3.89                  ( m1_subset_1 @
% 3.69/3.89                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 3.69/3.89                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 3.69/3.89    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 3.69/3.89  thf('0', plain,
% 3.69/3.89      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 3.69/3.89        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 3.69/3.89             sk_C)
% 3.69/3.89        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 3.69/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('1', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(redefinition_k2_partfun1, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.69/3.89     ( ( ( v1_funct_1 @ C ) & 
% 3.69/3.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.69/3.89       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 3.69/3.89  thf('2', plain,
% 3.69/3.89      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 3.69/3.89          | ~ (v1_funct_1 @ X57)
% 3.69/3.89          | ((k2_partfun1 @ X58 @ X59 @ X57 @ X60) = (k7_relat_1 @ X57 @ X60)))),
% 3.69/3.89      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 3.69/3.89  thf('3', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 3.69/3.89          | ~ (v1_funct_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['1', '2'])).
% 3.69/3.89  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('5', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.69/3.89  thf('6', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(dt_k2_partfun1, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.69/3.89     ( ( ( v1_funct_1 @ C ) & 
% 3.69/3.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.69/3.89       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.69/3.89         ( m1_subset_1 @
% 3.69/3.89           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.69/3.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.69/3.89  thf('7', plain,
% 3.69/3.89      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 3.69/3.89          | ~ (v1_funct_1 @ X53)
% 3.69/3.89          | (v1_funct_1 @ (k2_partfun1 @ X54 @ X55 @ X53 @ X56)))),
% 3.69/3.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.69/3.89  thf('8', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 3.69/3.89          | ~ (v1_funct_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['6', '7'])).
% 3.69/3.89  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('10', plain,
% 3.69/3.89      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['8', '9'])).
% 3.69/3.89  thf('11', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.69/3.89  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['10', '11'])).
% 3.69/3.89  thf('13', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.69/3.89  thf('14', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.69/3.89  thf('15', plain,
% 3.69/3.89      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 3.69/3.89        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 3.69/3.89      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.69/3.89  thf('16', plain,
% 3.69/3.89      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('17', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(redefinition_k7_relset_1, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.69/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.69/3.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.69/3.89  thf('18', plain,
% 3.69/3.89      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.69/3.89          | ((k7_relset_1 @ X39 @ X40 @ X38 @ X41) = (k9_relat_1 @ X38 @ X41)))),
% 3.69/3.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.69/3.89  thf('19', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('sup-', [status(thm)], ['17', '18'])).
% 3.69/3.89  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 3.69/3.89      inference('demod', [status(thm)], ['16', '19'])).
% 3.69/3.89  thf(t148_relat_1, axiom,
% 3.69/3.89    (![A:$i,B:$i]:
% 3.69/3.89     ( ( v1_relat_1 @ B ) =>
% 3.69/3.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.69/3.89  thf('21', plain,
% 3.69/3.89      (![X26 : $i, X27 : $i]:
% 3.69/3.89         (((k2_relat_1 @ (k7_relat_1 @ X26 @ X27)) = (k9_relat_1 @ X26 @ X27))
% 3.69/3.89          | ~ (v1_relat_1 @ X26))),
% 3.69/3.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.69/3.89  thf(d19_relat_1, axiom,
% 3.69/3.89    (![A:$i,B:$i]:
% 3.69/3.89     ( ( v1_relat_1 @ B ) =>
% 3.69/3.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.69/3.89  thf('22', plain,
% 3.69/3.89      (![X20 : $i, X21 : $i]:
% 3.69/3.89         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 3.69/3.89          | (v5_relat_1 @ X20 @ X21)
% 3.69/3.89          | ~ (v1_relat_1 @ X20))),
% 3.69/3.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.69/3.89  thf('23', plain,
% 3.69/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.69/3.89         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 3.69/3.89          | ~ (v1_relat_1 @ X1)
% 3.69/3.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.69/3.89          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 3.69/3.89      inference('sup-', [status(thm)], ['21', '22'])).
% 3.69/3.89  thf('24', plain,
% 3.69/3.89      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)
% 3.69/3.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 3.69/3.89        | ~ (v1_relat_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['20', '23'])).
% 3.69/3.89  thf('25', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('26', plain,
% 3.69/3.89      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 3.69/3.89          | ~ (v1_funct_1 @ X53)
% 3.69/3.89          | (m1_subset_1 @ (k2_partfun1 @ X54 @ X55 @ X53 @ X56) @ 
% 3.69/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 3.69/3.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.69/3.89  thf('27', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 3.69/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 3.69/3.89          | ~ (v1_funct_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['25', '26'])).
% 3.69/3.89  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('29', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 3.69/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('demod', [status(thm)], ['27', '28'])).
% 3.69/3.89  thf('30', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.69/3.89  thf('31', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 3.69/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('demod', [status(thm)], ['29', '30'])).
% 3.69/3.89  thf(cc2_relat_1, axiom,
% 3.69/3.89    (![A:$i]:
% 3.69/3.89     ( ( v1_relat_1 @ A ) =>
% 3.69/3.89       ( ![B:$i]:
% 3.69/3.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.69/3.89  thf('32', plain,
% 3.69/3.89      (![X16 : $i, X17 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 3.69/3.89          | (v1_relat_1 @ X16)
% 3.69/3.89          | ~ (v1_relat_1 @ X17))),
% 3.69/3.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.69/3.89  thf('33', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 3.69/3.89          | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 3.69/3.89      inference('sup-', [status(thm)], ['31', '32'])).
% 3.69/3.89  thf(fc6_relat_1, axiom,
% 3.69/3.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.69/3.89  thf('34', plain,
% 3.69/3.89      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 3.69/3.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.69/3.89  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['33', '34'])).
% 3.69/3.89  thf('36', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('37', plain,
% 3.69/3.89      (![X16 : $i, X17 : $i]:
% 3.69/3.89         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 3.69/3.89          | (v1_relat_1 @ X16)
% 3.69/3.89          | ~ (v1_relat_1 @ X17))),
% 3.69/3.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.69/3.89  thf('38', plain,
% 3.69/3.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['36', '37'])).
% 3.69/3.89  thf('39', plain,
% 3.69/3.89      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 3.69/3.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.69/3.89  thf('40', plain, ((v1_relat_1 @ sk_E)),
% 3.69/3.89      inference('demod', [status(thm)], ['38', '39'])).
% 3.69/3.89  thf('41', plain, ((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 3.69/3.89      inference('demod', [status(thm)], ['24', '35', '40'])).
% 3.69/3.89  thf('42', plain,
% 3.69/3.89      (![X20 : $i, X21 : $i]:
% 3.69/3.89         (~ (v5_relat_1 @ X20 @ X21)
% 3.69/3.89          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 3.69/3.89          | ~ (v1_relat_1 @ X20))),
% 3.69/3.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.69/3.89  thf('43', plain,
% 3.69/3.89      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 3.69/3.89        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C))),
% 3.69/3.89      inference('sup-', [status(thm)], ['41', '42'])).
% 3.69/3.89  thf('44', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.89      inference('demod', [status(thm)], ['33', '34'])).
% 3.69/3.89  thf('45', plain,
% 3.69/3.89      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)),
% 3.69/3.89      inference('demod', [status(thm)], ['43', '44'])).
% 3.69/3.89  thf(d10_xboole_0, axiom,
% 3.69/3.89    (![A:$i,B:$i]:
% 3.69/3.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.69/3.89  thf('46', plain,
% 3.69/3.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.69/3.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.69/3.89  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.69/3.89      inference('simplify', [status(thm)], ['46'])).
% 3.69/3.89  thf(t11_relset_1, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i]:
% 3.69/3.89     ( ( v1_relat_1 @ C ) =>
% 3.69/3.89       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 3.69/3.89           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 3.69/3.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.69/3.89  thf('48', plain,
% 3.69/3.89      (![X42 : $i, X43 : $i, X44 : $i]:
% 3.69/3.89         (~ (r1_tarski @ (k1_relat_1 @ X42) @ X43)
% 3.69/3.89          | ~ (r1_tarski @ (k2_relat_1 @ X42) @ X44)
% 3.69/3.89          | (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.69/3.89          | ~ (v1_relat_1 @ X42))),
% 3.69/3.89      inference('cnf', [status(esa)], [t11_relset_1])).
% 3.69/3.89  thf('49', plain,
% 3.69/3.89      (![X0 : $i, X1 : $i]:
% 3.69/3.89         (~ (v1_relat_1 @ X0)
% 3.69/3.89          | (m1_subset_1 @ X0 @ 
% 3.69/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 3.69/3.89          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 3.69/3.89      inference('sup-', [status(thm)], ['47', '48'])).
% 3.69/3.89  thf('50', plain,
% 3.69/3.89      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.89         (k1_zfmisc_1 @ 
% 3.69/3.89          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 3.69/3.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 3.69/3.89      inference('sup-', [status(thm)], ['45', '49'])).
% 3.69/3.89  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('52', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(d1_funct_2, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i]:
% 3.69/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.69/3.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.69/3.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.69/3.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.69/3.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.69/3.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.69/3.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.69/3.89  thf(zf_stmt_1, axiom,
% 3.69/3.89    (![C:$i,B:$i,A:$i]:
% 3.69/3.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.69/3.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.69/3.89  thf('53', plain,
% 3.69/3.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.69/3.89         (~ (v1_funct_2 @ X49 @ X47 @ X48)
% 3.69/3.89          | ((X47) = (k1_relset_1 @ X47 @ X48 @ X49))
% 3.69/3.89          | ~ (zip_tseitin_1 @ X49 @ X48 @ X47))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.69/3.89  thf('54', plain,
% 3.69/3.89      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 3.69/3.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 3.69/3.89      inference('sup-', [status(thm)], ['52', '53'])).
% 3.69/3.89  thf('55', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(redefinition_k1_relset_1, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i]:
% 3.69/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.69/3.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.69/3.89  thf('56', plain,
% 3.69/3.89      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.69/3.89         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 3.69/3.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 3.69/3.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.69/3.89  thf('57', plain,
% 3.69/3.89      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.69/3.89      inference('sup-', [status(thm)], ['55', '56'])).
% 3.69/3.89  thf('58', plain,
% 3.69/3.89      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 3.69/3.89      inference('demod', [status(thm)], ['54', '57'])).
% 3.69/3.89  thf(zf_stmt_2, axiom,
% 3.69/3.89    (![B:$i,A:$i]:
% 3.69/3.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.69/3.89       ( zip_tseitin_0 @ B @ A ) ))).
% 3.69/3.89  thf('59', plain,
% 3.69/3.89      (![X45 : $i, X46 : $i]:
% 3.69/3.89         ((zip_tseitin_0 @ X45 @ X46) | ((X45) = (k1_xboole_0)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.69/3.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.69/3.89  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.69/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.69/3.89  thf('61', plain,
% 3.69/3.89      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.69/3.89      inference('sup+', [status(thm)], ['59', '60'])).
% 3.69/3.89  thf('62', plain,
% 3.69/3.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.69/3.89  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.69/3.89  thf(zf_stmt_5, axiom,
% 3.69/3.89    (![A:$i,B:$i,C:$i]:
% 3.69/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.69/3.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.69/3.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.69/3.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.69/3.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.69/3.89  thf('63', plain,
% 3.69/3.89      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.69/3.89         (~ (zip_tseitin_0 @ X50 @ X51)
% 3.69/3.89          | (zip_tseitin_1 @ X52 @ X50 @ X51)
% 3.69/3.89          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50))))),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.69/3.89  thf('64', plain,
% 3.69/3.89      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 3.69/3.89      inference('sup-', [status(thm)], ['62', '63'])).
% 3.69/3.89  thf('65', plain,
% 3.69/3.89      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 3.69/3.89      inference('sup-', [status(thm)], ['61', '64'])).
% 3.69/3.89  thf('66', plain, (~ (v1_xboole_0 @ sk_D)),
% 3.69/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.69/3.89  thf('67', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 3.69/3.89      inference('clc', [status(thm)], ['65', '66'])).
% 3.69/3.89  thf('68', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 3.69/3.89      inference('demod', [status(thm)], ['58', '67'])).
% 3.69/3.89  thf(t91_relat_1, axiom,
% 3.69/3.89    (![A:$i,B:$i]:
% 3.69/3.89     ( ( v1_relat_1 @ B ) =>
% 3.69/3.89       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.69/3.89         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.69/3.89  thf('69', plain,
% 3.69/3.89      (![X30 : $i, X31 : $i]:
% 3.69/3.89         (~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 3.69/3.89          | ((k1_relat_1 @ (k7_relat_1 @ X31 @ X30)) = (X30))
% 3.69/3.89          | ~ (v1_relat_1 @ X31))),
% 3.69/3.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.69/3.89  thf('70', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (~ (r1_tarski @ X0 @ sk_A)
% 3.69/3.89          | ~ (v1_relat_1 @ sk_E)
% 3.69/3.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.69/3.89      inference('sup-', [status(thm)], ['68', '69'])).
% 3.69/3.89  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 3.69/3.89      inference('demod', [status(thm)], ['38', '39'])).
% 3.69/3.89  thf('72', plain,
% 3.69/3.89      (![X0 : $i]:
% 3.69/3.89         (~ (r1_tarski @ X0 @ sk_A)
% 3.69/3.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.69/3.89      inference('demod', [status(thm)], ['70', '71'])).
% 3.69/3.89  thf('73', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 3.69/3.89      inference('sup-', [status(thm)], ['51', '72'])).
% 3.69/3.89  thf('74', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 3.69/3.90      inference('demod', [status(thm)], ['33', '34'])).
% 3.69/3.90  thf('75', plain,
% 3.69/3.90      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.69/3.90      inference('demod', [status(thm)], ['50', '73', '74'])).
% 3.69/3.90  thf('76', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 3.69/3.90      inference('demod', [status(thm)], ['15', '75'])).
% 3.69/3.90  thf('77', plain,
% 3.69/3.90      (![X45 : $i, X46 : $i]:
% 3.69/3.90         ((zip_tseitin_0 @ X45 @ X46) | ((X45) = (k1_xboole_0)))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.69/3.90  thf('78', plain,
% 3.69/3.90      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.69/3.90      inference('demod', [status(thm)], ['50', '73', '74'])).
% 3.69/3.90  thf('79', plain,
% 3.69/3.90      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.69/3.90         (~ (zip_tseitin_0 @ X50 @ X51)
% 3.69/3.90          | (zip_tseitin_1 @ X52 @ X50 @ X51)
% 3.69/3.90          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50))))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.69/3.90  thf('80', plain,
% 3.69/3.90      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 3.69/3.90        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.69/3.90      inference('sup-', [status(thm)], ['78', '79'])).
% 3.69/3.90  thf('81', plain,
% 3.69/3.90      ((((sk_C) = (k1_xboole_0))
% 3.69/3.90        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 3.69/3.90      inference('sup-', [status(thm)], ['77', '80'])).
% 3.69/3.90  thf('82', plain,
% 3.69/3.90      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.69/3.90      inference('demod', [status(thm)], ['50', '73', '74'])).
% 3.69/3.90  thf('83', plain,
% 3.69/3.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.69/3.90         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 3.69/3.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 3.69/3.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.69/3.90  thf('84', plain,
% 3.69/3.90      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 3.69/3.90         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 3.69/3.90      inference('sup-', [status(thm)], ['82', '83'])).
% 3.69/3.90  thf('85', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 3.69/3.90      inference('sup-', [status(thm)], ['51', '72'])).
% 3.69/3.90  thf('86', plain,
% 3.69/3.90      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 3.69/3.90      inference('demod', [status(thm)], ['84', '85'])).
% 3.69/3.90  thf('87', plain,
% 3.69/3.90      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.69/3.90         (((X47) != (k1_relset_1 @ X47 @ X48 @ X49))
% 3.69/3.90          | (v1_funct_2 @ X49 @ X47 @ X48)
% 3.69/3.90          | ~ (zip_tseitin_1 @ X49 @ X48 @ X47))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.69/3.90  thf('88', plain,
% 3.69/3.90      ((((sk_B) != (sk_B))
% 3.69/3.90        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 3.69/3.90        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 3.69/3.90      inference('sup-', [status(thm)], ['86', '87'])).
% 3.69/3.90  thf('89', plain,
% 3.69/3.90      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 3.69/3.90        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 3.69/3.90      inference('simplify', [status(thm)], ['88'])).
% 3.69/3.90  thf('90', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 3.69/3.90      inference('demod', [status(thm)], ['15', '75'])).
% 3.69/3.90  thf('91', plain,
% 3.69/3.90      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 3.69/3.90      inference('clc', [status(thm)], ['89', '90'])).
% 3.69/3.90  thf('92', plain, (((sk_C) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['81', '91'])).
% 3.69/3.90  thf('93', plain,
% 3.69/3.90      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 3.69/3.90      inference('demod', [status(thm)], ['76', '92'])).
% 3.69/3.90  thf('94', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 3.69/3.90      inference('sup-', [status(thm)], ['51', '72'])).
% 3.69/3.90  thf('95', plain,
% 3.69/3.90      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.69/3.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.69/3.90      inference('demod', [status(thm)], ['50', '73', '74'])).
% 3.69/3.90  thf(t3_subset, axiom,
% 3.69/3.90    (![A:$i,B:$i]:
% 3.69/3.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.69/3.90  thf('96', plain,
% 3.69/3.90      (![X13 : $i, X14 : $i]:
% 3.69/3.90         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.69/3.90      inference('cnf', [status(esa)], [t3_subset])).
% 3.69/3.90  thf('97', plain,
% 3.69/3.90      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 3.69/3.90      inference('sup-', [status(thm)], ['95', '96'])).
% 3.69/3.90  thf('98', plain,
% 3.69/3.90      (![X0 : $i, X2 : $i]:
% 3.69/3.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.69/3.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.69/3.90  thf('99', plain,
% 3.69/3.90      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_C) @ (k7_relat_1 @ sk_E @ sk_B))
% 3.69/3.90        | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_E @ sk_B)))),
% 3.69/3.90      inference('sup-', [status(thm)], ['97', '98'])).
% 3.69/3.90  thf('100', plain, (((sk_C) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['81', '91'])).
% 3.69/3.90  thf(t113_zfmisc_1, axiom,
% 3.69/3.90    (![A:$i,B:$i]:
% 3.69/3.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.69/3.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.69/3.90  thf('101', plain,
% 3.69/3.90      (![X11 : $i, X12 : $i]:
% 3.69/3.90         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.69/3.90          | ((X12) != (k1_xboole_0)))),
% 3.69/3.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.69/3.90  thf('102', plain,
% 3.69/3.90      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['101'])).
% 3.69/3.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.69/3.90  thf('103', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.69/3.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.69/3.90  thf('104', plain, (((sk_C) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['81', '91'])).
% 3.69/3.90  thf('105', plain,
% 3.69/3.90      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['101'])).
% 3.69/3.90  thf('106', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 3.69/3.90      inference('demod', [status(thm)],
% 3.69/3.90                ['99', '100', '102', '103', '104', '105'])).
% 3.69/3.90  thf('107', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_B))),
% 3.69/3.90      inference('demod', [status(thm)], ['94', '106'])).
% 3.69/3.90  thf('108', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.69/3.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.69/3.90  thf('109', plain,
% 3.69/3.90      (![X13 : $i, X15 : $i]:
% 3.69/3.90         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.69/3.90      inference('cnf', [status(esa)], [t3_subset])).
% 3.69/3.90  thf('110', plain,
% 3.69/3.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['108', '109'])).
% 3.69/3.90  thf(cc2_relset_1, axiom,
% 3.69/3.90    (![A:$i,B:$i,C:$i]:
% 3.69/3.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.69/3.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.69/3.90  thf('111', plain,
% 3.69/3.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.69/3.90         ((v4_relat_1 @ X32 @ X33)
% 3.69/3.90          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 3.69/3.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.69/3.90  thf('112', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.69/3.90      inference('sup-', [status(thm)], ['110', '111'])).
% 3.69/3.90  thf(d18_relat_1, axiom,
% 3.69/3.90    (![A:$i,B:$i]:
% 3.69/3.90     ( ( v1_relat_1 @ B ) =>
% 3.69/3.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.69/3.90  thf('113', plain,
% 3.69/3.90      (![X18 : $i, X19 : $i]:
% 3.69/3.90         (~ (v4_relat_1 @ X18 @ X19)
% 3.69/3.90          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 3.69/3.90          | ~ (v1_relat_1 @ X18))),
% 3.69/3.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.69/3.90  thf('114', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         (~ (v1_relat_1 @ k1_xboole_0)
% 3.69/3.90          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['112', '113'])).
% 3.69/3.90  thf('115', plain,
% 3.69/3.90      (![X11 : $i, X12 : $i]:
% 3.69/3.90         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.69/3.90          | ((X11) != (k1_xboole_0)))),
% 3.69/3.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.69/3.90  thf('116', plain,
% 3.69/3.90      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['115'])).
% 3.69/3.90  thf('117', plain,
% 3.69/3.90      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 3.69/3.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.69/3.90  thf('118', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.69/3.90      inference('sup+', [status(thm)], ['116', '117'])).
% 3.69/3.90  thf('119', plain,
% 3.69/3.90      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.69/3.90      inference('demod', [status(thm)], ['114', '118'])).
% 3.69/3.90  thf(t3_xboole_1, axiom,
% 3.69/3.90    (![A:$i]:
% 3.69/3.90     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.69/3.90  thf('120', plain,
% 3.69/3.90      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 3.69/3.90      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.69/3.90  thf('121', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['119', '120'])).
% 3.69/3.90  thf('122', plain, (((sk_B) = (k1_xboole_0))),
% 3.69/3.90      inference('sup+', [status(thm)], ['107', '121'])).
% 3.69/3.90  thf(dt_k7_relat_1, axiom,
% 3.69/3.90    (![A:$i,B:$i]:
% 3.69/3.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.69/3.90  thf('123', plain,
% 3.69/3.90      (![X22 : $i, X23 : $i]:
% 3.69/3.90         (~ (v1_relat_1 @ X22) | (v1_relat_1 @ (k7_relat_1 @ X22 @ X23)))),
% 3.69/3.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.69/3.90  thf('124', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.69/3.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.69/3.90  thf('125', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         (~ (r1_tarski @ X0 @ sk_A)
% 3.69/3.90          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.69/3.90      inference('demod', [status(thm)], ['70', '71'])).
% 3.69/3.90  thf('126', plain,
% 3.69/3.90      (((k1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['124', '125'])).
% 3.69/3.90  thf('127', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.69/3.90      inference('simplify', [status(thm)], ['46'])).
% 3.69/3.90  thf('128', plain,
% 3.69/3.90      (![X0 : $i, X1 : $i]:
% 3.69/3.90         (~ (v1_relat_1 @ X0)
% 3.69/3.90          | (m1_subset_1 @ X0 @ 
% 3.69/3.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 3.69/3.90          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 3.69/3.90      inference('sup-', [status(thm)], ['47', '48'])).
% 3.69/3.90  thf('129', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         ((m1_subset_1 @ X0 @ 
% 3.69/3.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 3.69/3.90          | ~ (v1_relat_1 @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['127', '128'])).
% 3.69/3.90  thf('130', plain,
% 3.69/3.90      (![X13 : $i, X14 : $i]:
% 3.69/3.90         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.69/3.90      inference('cnf', [status(esa)], [t3_subset])).
% 3.69/3.90  thf('131', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         (~ (v1_relat_1 @ X0)
% 3.69/3.90          | (r1_tarski @ X0 @ 
% 3.69/3.90             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 3.69/3.90      inference('sup-', [status(thm)], ['129', '130'])).
% 3.69/3.90  thf('132', plain,
% 3.69/3.90      (![X0 : $i, X2 : $i]:
% 3.69/3.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.69/3.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.69/3.90  thf('133', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         (~ (v1_relat_1 @ X0)
% 3.69/3.90          | ~ (r1_tarski @ 
% 3.69/3.90               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 3.69/3.90          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 3.69/3.90      inference('sup-', [status(thm)], ['131', '132'])).
% 3.69/3.90  thf('134', plain,
% 3.69/3.90      ((~ (r1_tarski @ 
% 3.69/3.90           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 3.69/3.90            (k2_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0))) @ 
% 3.69/3.90           (k7_relat_1 @ sk_E @ k1_xboole_0))
% 3.69/3.90        | ((k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)) @ 
% 3.69/3.90            (k2_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))
% 3.69/3.90            = (k7_relat_1 @ sk_E @ k1_xboole_0))
% 3.69/3.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 3.69/3.90      inference('sup-', [status(thm)], ['126', '133'])).
% 3.69/3.90  thf('135', plain,
% 3.69/3.90      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['115'])).
% 3.69/3.90  thf('136', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.69/3.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.69/3.90  thf('137', plain,
% 3.69/3.90      (((k1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['124', '125'])).
% 3.69/3.90  thf('138', plain,
% 3.69/3.90      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['115'])).
% 3.69/3.90  thf('139', plain,
% 3.69/3.90      ((((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))
% 3.69/3.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 3.69/3.90      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 3.69/3.90  thf('140', plain,
% 3.69/3.90      ((~ (v1_relat_1 @ sk_E)
% 3.69/3.90        | ((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 3.69/3.90      inference('sup-', [status(thm)], ['123', '139'])).
% 3.69/3.90  thf('141', plain, ((v1_relat_1 @ sk_E)),
% 3.69/3.90      inference('demod', [status(thm)], ['38', '39'])).
% 3.69/3.90  thf('142', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 3.69/3.90      inference('demod', [status(thm)], ['140', '141'])).
% 3.69/3.90  thf('143', plain, (((sk_B) = (k1_xboole_0))),
% 3.69/3.90      inference('sup+', [status(thm)], ['107', '121'])).
% 3.69/3.90  thf('144', plain,
% 3.69/3.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['108', '109'])).
% 3.69/3.90  thf('145', plain,
% 3.69/3.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.69/3.90         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 3.69/3.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 3.69/3.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.69/3.90  thf('146', plain,
% 3.69/3.90      (![X0 : $i, X1 : $i]:
% 3.69/3.90         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['144', '145'])).
% 3.69/3.90  thf('147', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['119', '120'])).
% 3.69/3.90  thf('148', plain,
% 3.69/3.90      (![X0 : $i, X1 : $i]:
% 3.69/3.90         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.69/3.90      inference('demod', [status(thm)], ['146', '147'])).
% 3.69/3.90  thf('149', plain,
% 3.69/3.90      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.69/3.90         (((X47) != (k1_relset_1 @ X47 @ X48 @ X49))
% 3.69/3.90          | (v1_funct_2 @ X49 @ X47 @ X48)
% 3.69/3.90          | ~ (zip_tseitin_1 @ X49 @ X48 @ X47))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.69/3.90  thf('150', plain,
% 3.69/3.90      (![X0 : $i, X1 : $i]:
% 3.69/3.90         (((X1) != (k1_xboole_0))
% 3.69/3.90          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.69/3.90          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['148', '149'])).
% 3.69/3.90  thf('151', plain,
% 3.69/3.90      (![X0 : $i]:
% 3.69/3.90         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.69/3.90          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.69/3.90      inference('simplify', [status(thm)], ['150'])).
% 3.69/3.90  thf('152', plain,
% 3.69/3.90      (![X45 : $i, X46 : $i]:
% 3.69/3.90         ((zip_tseitin_0 @ X45 @ X46) | ((X46) != (k1_xboole_0)))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.69/3.90  thf('153', plain, (![X45 : $i]: (zip_tseitin_0 @ X45 @ k1_xboole_0)),
% 3.69/3.90      inference('simplify', [status(thm)], ['152'])).
% 3.69/3.90  thf('154', plain,
% 3.69/3.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.69/3.90      inference('sup-', [status(thm)], ['108', '109'])).
% 3.69/3.90  thf('155', plain,
% 3.69/3.90      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.69/3.90         (~ (zip_tseitin_0 @ X50 @ X51)
% 3.69/3.90          | (zip_tseitin_1 @ X52 @ X50 @ X51)
% 3.69/3.90          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50))))),
% 3.69/3.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.69/3.90  thf('156', plain,
% 3.69/3.90      (![X0 : $i, X1 : $i]:
% 3.69/3.90         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.69/3.90      inference('sup-', [status(thm)], ['154', '155'])).
% 3.69/3.90  thf('157', plain,
% 3.69/3.90      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.69/3.90      inference('sup-', [status(thm)], ['153', '156'])).
% 3.69/3.90  thf('158', plain,
% 3.69/3.90      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.69/3.90      inference('demod', [status(thm)], ['151', '157'])).
% 3.69/3.90  thf('159', plain, ($false),
% 3.69/3.90      inference('demod', [status(thm)], ['93', '122', '142', '143', '158'])).
% 3.69/3.90  
% 3.69/3.90  % SZS output end Refutation
% 3.69/3.90  
% 3.69/3.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
