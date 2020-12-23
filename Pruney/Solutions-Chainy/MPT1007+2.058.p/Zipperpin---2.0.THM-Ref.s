%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.te3BYVxYHb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 268 expanded)
%              Number of leaves         :   51 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  738 (2646 expanded)
%              Number of equality atoms :   70 ( 203 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
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

thf('1',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ~ ( v1_funct_2 @ X75 @ X73 @ X74 )
      | ( X73
        = ( k1_relset_1 @ X73 @ X74 @ X75 ) )
      | ~ ( zip_tseitin_1 @ X75 @ X74 @ X73 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X71: $i,X72: $i] :
      ( ( zip_tseitin_0 @ X71 @ X72 )
      | ( X71 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X71: $i,X72: $i] :
      ( ( zip_tseitin_0 @ X71 @ X72 )
      | ( X71 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
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

thf('7',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ~ ( zip_tseitin_0 @ X76 @ X77 )
      | ( zip_tseitin_1 @ X78 @ X76 @ X77 )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X77 @ X76 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    sk_B_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X67 @ X65 )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','13','16'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('18',plain,(
    ! [X57: $i] :
      ( ( k1_ordinal1 @ X57 )
      = ( k2_xboole_0 @ X57 @ ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('19',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','13','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X35 @ X36 ) )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) )
        = X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( o_0_0_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','13','16'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( o_0_0_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','13','16'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X62 @ X63 @ X64 ) @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_2 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( ( k2_relset_1 @ X69 @ X70 @ X68 )
        = ( k2_relat_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','13','16'])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_2 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('48',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( ( k8_relat_1 @ X47 @ X46 )
        = X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k8_relat_1 @ sk_B_2 @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( v1_relat_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k8_relat_1 @ sk_B_2 @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['49','52'])).

thf(t86_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('54',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X54 @ ( k1_relat_1 @ ( k8_relat_1 @ X56 @ X55 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X55 @ X54 ) @ X56 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( o_0_0_xboole_0
      = ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','58'])).

thf('60',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ o_0_0_xboole_0 )
      = X3 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['19','61','64'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('66',plain,(
    ! [X58: $i] :
      ( X58
     != ( k1_ordinal1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.te3BYVxYHb
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:18:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 175 iterations in 0.054s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(t61_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.50         ( m1_subset_1 @
% 0.20/0.50           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.50            ( m1_subset_1 @
% 0.20/0.50              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.20/0.50  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d1_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, axiom,
% 0.20/0.50    (![C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.20/0.50         (~ (v1_funct_2 @ X75 @ X73 @ X74)
% 0.20/0.50          | ((X73) = (k1_relset_1 @ X73 @ X74 @ X75))
% 0.20/0.50          | ~ (zip_tseitin_1 @ X75 @ X74 @ X73))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.20/0.50        | ((k1_tarski @ sk_A)
% 0.20/0.50            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(zf_stmt_2, axiom,
% 0.20/0.50    (![B:$i,A:$i]:
% 0.20/0.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X71 : $i, X72 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X71 @ X72) | ((X71) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.50  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.50  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X71 : $i, X72 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X71 @ X72) | ((X71) = (o_0_0_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_5, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X76 : $i, X77 : $i, X78 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X76 @ X77)
% 0.20/0.50          | (zip_tseitin_1 @ X78 @ X76 @ X77)
% 0.20/0.50          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X77 @ X76))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.20/0.50        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((((sk_B_2) = (o_0_0_xboole_0))
% 0.20/0.50        | (zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.50  thf('10', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.50  thf('12', plain, (((sk_B_2) != (o_0_0_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X66 @ X67 @ X65) = (k1_relat_1 @ X65))
% 0.20/0.50          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)
% 0.20/0.50         = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '13', '16'])).
% 0.20/0.50  thf(d1_ordinal1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X57 : $i]:
% 0.20/0.50         ((k1_ordinal1 @ X57) = (k2_xboole_0 @ X57 @ (k1_tarski @ X57)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((k1_ordinal1 @ sk_A) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '13', '16'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('21', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t19_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.50       ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ (k1_tarski @ X35) @ (k2_tarski @ X35 @ X36))
% 0.20/0.50           = (k1_tarski @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           = (k1_tarski @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(t92_xboole_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('26', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.50  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.50  thf('28', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50           = (o_0_0_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf(t65_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X38 : $i, X39 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X38 @ (k1_tarski @ X39)) = (X38))
% 0.20/0.50          | (r2_hidden @ X39 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((o_0_0_xboole_0) = (k1_tarski @ X0))
% 0.20/0.50          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.50        | ((o_0_0_xboole_0) = (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['20', '31'])).
% 0.20/0.50  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '13', '16'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.50        | ((o_0_0_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '13', '16'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf(dt_k2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k2_relset_1 @ X62 @ X63 @ X64) @ (k1_zfmisc_1 @ X63))
% 0.20/0.50          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((m1_subset_1 @ (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B_2 @ sk_C) @ 
% 0.20/0.50        (k1_zfmisc_1 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.20/0.50         (((k2_relset_1 @ X69 @ X70 @ X68) = (k2_relat_1 @ X68))
% 0.20/0.50          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)
% 0.20/0.50         = (k2_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '13', '16'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B_2 @ sk_C)
% 0.20/0.50         = (k2_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '44'])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X43 : $i, X44 : $i]:
% 0.20/0.50         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf(t125_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X46 : $i, X47 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.20/0.50          | ((k8_relat_1 @ X47 @ X46) = (X46))
% 0.20/0.50          | ~ (v1_relat_1 @ X46))),
% 0.20/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_C) | ((k8_relat_1 @ sk_B_2 @ sk_C) = (sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( v1_relat_1 @ C ) ))).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X59)
% 0.20/0.50          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, (((k8_relat_1 @ sk_B_2 @ sk_C) = (sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '52'])).
% 0.20/0.50  thf(t86_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.20/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.50           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X54 @ (k1_relat_1 @ (k8_relat_1 @ X56 @ X55)))
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ X55 @ X54) @ X56)
% 0.20/0.50          | ~ (v1_funct_1 @ X55)
% 0.20/0.50          | ~ (v1_relat_1 @ X55))),
% 0.20/0.50      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.20/0.50          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((((o_0_0_xboole_0) = (k1_relat_1 @ sk_C))
% 0.20/0.50        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '58'])).
% 0.20/0.50  thf('60', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf(t1_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('62', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.50  thf('63', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.50  thf('64', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ o_0_0_xboole_0) = (X3))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '61', '64'])).
% 0.20/0.50  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.20/0.50  thf('66', plain, (![X58 : $i]: ((X58) != (k1_ordinal1 @ X58))),
% 0.20/0.50      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.20/0.50  thf('67', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
