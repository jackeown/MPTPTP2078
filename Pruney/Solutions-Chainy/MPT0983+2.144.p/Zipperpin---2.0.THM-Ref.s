%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hfquJGthgV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:24 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 310 expanded)
%              Number of leaves         :   39 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          : 1042 (6304 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('1',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('5',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
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

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_partfun1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != X20 )
      | ( v2_funct_2 @ X21 @ X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('28',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
      | ( v2_funct_2 @ X21 @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['29','32','33','38'])).

thf('40',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['11','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('61',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('62',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33 ) )
      | ( v2_funct_1 @ X37 )
      | ( X35 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X34 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['47','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['44','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hfquJGthgV
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.92/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.92/2.13  % Solved by: fo/fo7.sh
% 1.92/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.13  % done 1600 iterations in 1.679s
% 1.92/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.92/2.13  % SZS output start Refutation
% 1.92/2.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.92/2.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.92/2.13  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.92/2.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.92/2.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.92/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.92/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.92/2.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.92/2.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.92/2.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.92/2.13  thf(sk_C_type, type, sk_C: $i).
% 1.92/2.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.92/2.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.92/2.13  thf(sk_D_type, type, sk_D: $i).
% 1.92/2.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.92/2.13  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.92/2.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.92/2.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.92/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.92/2.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.92/2.13  thf(l13_xboole_0, axiom,
% 1.92/2.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.92/2.13  thf('0', plain,
% 1.92/2.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.92/2.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.92/2.13  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.92/2.13  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.92/2.13      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.92/2.13  thf(redefinition_k6_partfun1, axiom,
% 1.92/2.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.92/2.13  thf('2', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.92/2.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.92/2.13  thf('3', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.92/2.13      inference('demod', [status(thm)], ['1', '2'])).
% 1.92/2.13  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.92/2.13  thf('4', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 1.92/2.13      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.92/2.13  thf('5', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.92/2.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.92/2.13  thf('6', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 1.92/2.13      inference('demod', [status(thm)], ['4', '5'])).
% 1.92/2.13  thf('7', plain, ((v2_funct_1 @ k1_xboole_0)),
% 1.92/2.13      inference('sup+', [status(thm)], ['3', '6'])).
% 1.92/2.13  thf('8', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.92/2.13      inference('sup+', [status(thm)], ['0', '7'])).
% 1.92/2.13  thf(t29_funct_2, conjecture,
% 1.92/2.13    (![A:$i,B:$i,C:$i]:
% 1.92/2.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.92/2.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.92/2.13       ( ![D:$i]:
% 1.92/2.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.92/2.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.92/2.13           ( ( r2_relset_1 @
% 1.92/2.13               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.92/2.13               ( k6_partfun1 @ A ) ) =>
% 1.92/2.13             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.92/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.13    (~( ![A:$i,B:$i,C:$i]:
% 1.92/2.13        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.92/2.13            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.92/2.13          ( ![D:$i]:
% 1.92/2.13            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.92/2.13                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.92/2.13              ( ( r2_relset_1 @
% 1.92/2.13                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.92/2.13                  ( k6_partfun1 @ A ) ) =>
% 1.92/2.13                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.92/2.13    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.92/2.13  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.92/2.13      inference('split', [status(esa)], ['9'])).
% 1.92/2.13  thf('11', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.92/2.13      inference('sup-', [status(thm)], ['8', '10'])).
% 1.92/2.13  thf('12', plain,
% 1.92/2.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.92/2.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.92/2.13        (k6_partfun1 @ sk_A))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('13', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(t24_funct_2, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i]:
% 1.92/2.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.92/2.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.92/2.13       ( ![D:$i]:
% 1.92/2.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.92/2.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.92/2.13           ( ( r2_relset_1 @
% 1.92/2.13               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.92/2.13               ( k6_partfun1 @ B ) ) =>
% 1.92/2.13             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.92/2.13  thf('14', plain,
% 1.92/2.13      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X29)
% 1.92/2.13          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 1.92/2.13          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.92/2.13          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.92/2.13               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 1.92/2.13               (k6_partfun1 @ X30))
% 1.92/2.13          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 1.92/2.13          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.92/2.13          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.92/2.13          | ~ (v1_funct_1 @ X32))),
% 1.92/2.13      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.92/2.13  thf('15', plain,
% 1.92/2.13      (![X0 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X0)
% 1.92/2.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.92/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.92/2.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.92/2.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.92/2.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.92/2.13               (k6_partfun1 @ sk_A))
% 1.92/2.13          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.92/2.13          | ~ (v1_funct_1 @ sk_C))),
% 1.92/2.13      inference('sup-', [status(thm)], ['13', '14'])).
% 1.92/2.13  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('18', plain,
% 1.92/2.13      (![X0 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X0)
% 1.92/2.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.92/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.92/2.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.92/2.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.92/2.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.92/2.13               (k6_partfun1 @ sk_A)))),
% 1.92/2.13      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.92/2.13  thf('19', plain,
% 1.92/2.13      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.92/2.13        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.92/2.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.92/2.13        | ~ (v1_funct_1 @ sk_D))),
% 1.92/2.13      inference('sup-', [status(thm)], ['12', '18'])).
% 1.92/2.13  thf('20', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(redefinition_k2_relset_1, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i]:
% 1.92/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.92/2.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.92/2.13  thf('21', plain,
% 1.92/2.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.92/2.13         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.92/2.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.92/2.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.92/2.13  thf('22', plain,
% 1.92/2.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.92/2.13      inference('sup-', [status(thm)], ['20', '21'])).
% 1.92/2.13  thf('23', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('26', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.92/2.13      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 1.92/2.13  thf(d3_funct_2, axiom,
% 1.92/2.13    (![A:$i,B:$i]:
% 1.92/2.13     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.92/2.13       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.92/2.13  thf('27', plain,
% 1.92/2.13      (![X20 : $i, X21 : $i]:
% 1.92/2.13         (((k2_relat_1 @ X21) != (X20))
% 1.92/2.13          | (v2_funct_2 @ X21 @ X20)
% 1.92/2.13          | ~ (v5_relat_1 @ X21 @ X20)
% 1.92/2.13          | ~ (v1_relat_1 @ X21))),
% 1.92/2.13      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.92/2.13  thf('28', plain,
% 1.92/2.13      (![X21 : $i]:
% 1.92/2.13         (~ (v1_relat_1 @ X21)
% 1.92/2.13          | ~ (v5_relat_1 @ X21 @ (k2_relat_1 @ X21))
% 1.92/2.13          | (v2_funct_2 @ X21 @ (k2_relat_1 @ X21)))),
% 1.92/2.13      inference('simplify', [status(thm)], ['27'])).
% 1.92/2.13  thf('29', plain,
% 1.92/2.13      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.92/2.13        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.92/2.13        | ~ (v1_relat_1 @ sk_D))),
% 1.92/2.13      inference('sup-', [status(thm)], ['26', '28'])).
% 1.92/2.13  thf('30', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(cc2_relset_1, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i]:
% 1.92/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.92/2.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.92/2.13  thf('31', plain,
% 1.92/2.13      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.92/2.13         ((v5_relat_1 @ X6 @ X8)
% 1.92/2.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.92/2.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.92/2.13  thf('32', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.92/2.13      inference('sup-', [status(thm)], ['30', '31'])).
% 1.92/2.13  thf('33', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.92/2.13      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 1.92/2.13  thf('34', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(cc2_relat_1, axiom,
% 1.92/2.13    (![A:$i]:
% 1.92/2.13     ( ( v1_relat_1 @ A ) =>
% 1.92/2.13       ( ![B:$i]:
% 1.92/2.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.92/2.13  thf('35', plain,
% 1.92/2.13      (![X1 : $i, X2 : $i]:
% 1.92/2.13         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.92/2.13          | (v1_relat_1 @ X1)
% 1.92/2.13          | ~ (v1_relat_1 @ X2))),
% 1.92/2.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.92/2.13  thf('36', plain,
% 1.92/2.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.92/2.13      inference('sup-', [status(thm)], ['34', '35'])).
% 1.92/2.13  thf(fc6_relat_1, axiom,
% 1.92/2.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.92/2.13  thf('37', plain,
% 1.92/2.13      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.92/2.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.92/2.13  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 1.92/2.13      inference('demod', [status(thm)], ['36', '37'])).
% 1.92/2.13  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.92/2.13      inference('demod', [status(thm)], ['29', '32', '33', '38'])).
% 1.92/2.13  thf('40', plain,
% 1.92/2.13      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.92/2.13      inference('split', [status(esa)], ['9'])).
% 1.92/2.13  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.92/2.13      inference('sup-', [status(thm)], ['39', '40'])).
% 1.92/2.13  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.92/2.13      inference('split', [status(esa)], ['9'])).
% 1.92/2.13  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.92/2.13      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 1.92/2.13  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.92/2.13      inference('simpl_trail', [status(thm)], ['11', '43'])).
% 1.92/2.13  thf('45', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(cc3_relset_1, axiom,
% 1.92/2.13    (![A:$i,B:$i]:
% 1.92/2.13     ( ( v1_xboole_0 @ A ) =>
% 1.92/2.13       ( ![C:$i]:
% 1.92/2.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.92/2.13           ( v1_xboole_0 @ C ) ) ) ))).
% 1.92/2.13  thf('46', plain,
% 1.92/2.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.92/2.13         (~ (v1_xboole_0 @ X9)
% 1.92/2.13          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 1.92/2.13          | (v1_xboole_0 @ X10))),
% 1.92/2.13      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.92/2.13  thf('47', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.92/2.13      inference('sup-', [status(thm)], ['45', '46'])).
% 1.92/2.13  thf('48', plain,
% 1.92/2.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.92/2.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.92/2.13        (k6_partfun1 @ sk_A))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('49', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('50', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(dt_k1_partfun1, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.92/2.13     ( ( ( v1_funct_1 @ E ) & 
% 1.92/2.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.92/2.13         ( v1_funct_1 @ F ) & 
% 1.92/2.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.92/2.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.92/2.13         ( m1_subset_1 @
% 1.92/2.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.92/2.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.92/2.13  thf('51', plain,
% 1.92/2.13      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.92/2.13         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.92/2.13          | ~ (v1_funct_1 @ X22)
% 1.92/2.13          | ~ (v1_funct_1 @ X25)
% 1.92/2.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.92/2.13          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.92/2.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.92/2.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.92/2.13  thf('52', plain,
% 1.92/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.92/2.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.92/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.92/2.13          | ~ (v1_funct_1 @ X1)
% 1.92/2.13          | ~ (v1_funct_1 @ sk_C))),
% 1.92/2.13      inference('sup-', [status(thm)], ['50', '51'])).
% 1.92/2.13  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('54', plain,
% 1.92/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.92/2.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.92/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.92/2.13          | ~ (v1_funct_1 @ X1))),
% 1.92/2.13      inference('demod', [status(thm)], ['52', '53'])).
% 1.92/2.13  thf('55', plain,
% 1.92/2.13      ((~ (v1_funct_1 @ sk_D)
% 1.92/2.13        | (m1_subset_1 @ 
% 1.92/2.13           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.92/2.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.92/2.13      inference('sup-', [status(thm)], ['49', '54'])).
% 1.92/2.13  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('57', plain,
% 1.92/2.13      ((m1_subset_1 @ 
% 1.92/2.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.92/2.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.92/2.13      inference('demod', [status(thm)], ['55', '56'])).
% 1.92/2.13  thf(redefinition_r2_relset_1, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i,D:$i]:
% 1.92/2.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.92/2.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.92/2.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.92/2.13  thf('58', plain,
% 1.92/2.13      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.92/2.13         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.92/2.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.92/2.13          | ((X15) = (X18))
% 1.92/2.13          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 1.92/2.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.92/2.13  thf('59', plain,
% 1.92/2.13      (![X0 : $i]:
% 1.92/2.13         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.92/2.13             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.92/2.13          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.92/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.92/2.13      inference('sup-', [status(thm)], ['57', '58'])).
% 1.92/2.13  thf('60', plain,
% 1.92/2.13      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.92/2.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.92/2.13        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.92/2.13            = (k6_partfun1 @ sk_A)))),
% 1.92/2.13      inference('sup-', [status(thm)], ['48', '59'])).
% 1.92/2.13  thf(t29_relset_1, axiom,
% 1.92/2.13    (![A:$i]:
% 1.92/2.13     ( m1_subset_1 @
% 1.92/2.13       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.92/2.13  thf('61', plain,
% 1.92/2.13      (![X19 : $i]:
% 1.92/2.13         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 1.92/2.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.92/2.13      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.92/2.13  thf('62', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.92/2.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.92/2.13  thf('63', plain,
% 1.92/2.13      (![X19 : $i]:
% 1.92/2.13         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 1.92/2.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.92/2.13      inference('demod', [status(thm)], ['61', '62'])).
% 1.92/2.13  thf('64', plain,
% 1.92/2.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.92/2.13         = (k6_partfun1 @ sk_A))),
% 1.92/2.13      inference('demod', [status(thm)], ['60', '63'])).
% 1.92/2.13  thf('65', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf(t26_funct_2, axiom,
% 1.92/2.13    (![A:$i,B:$i,C:$i,D:$i]:
% 1.92/2.13     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.92/2.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.92/2.13       ( ![E:$i]:
% 1.92/2.13         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.92/2.13             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.92/2.13           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.92/2.13             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.92/2.13               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.92/2.13  thf('66', plain,
% 1.92/2.13      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X33)
% 1.92/2.13          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.92/2.13          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.92/2.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33))
% 1.92/2.13          | (v2_funct_1 @ X37)
% 1.92/2.13          | ((X35) = (k1_xboole_0))
% 1.92/2.13          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 1.92/2.13          | ~ (v1_funct_2 @ X37 @ X36 @ X34)
% 1.92/2.13          | ~ (v1_funct_1 @ X37))),
% 1.92/2.13      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.92/2.13  thf('67', plain,
% 1.92/2.13      (![X0 : $i, X1 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X0)
% 1.92/2.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.92/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.92/2.13          | ((sk_A) = (k1_xboole_0))
% 1.92/2.13          | (v2_funct_1 @ X0)
% 1.92/2.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.92/2.13          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.92/2.13          | ~ (v1_funct_1 @ sk_D))),
% 1.92/2.13      inference('sup-', [status(thm)], ['65', '66'])).
% 1.92/2.13  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('70', plain,
% 1.92/2.13      (![X0 : $i, X1 : $i]:
% 1.92/2.13         (~ (v1_funct_1 @ X0)
% 1.92/2.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.92/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.92/2.13          | ((sk_A) = (k1_xboole_0))
% 1.92/2.13          | (v2_funct_1 @ X0)
% 1.92/2.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.92/2.13      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.92/2.13  thf('71', plain,
% 1.92/2.13      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.92/2.13        | (v2_funct_1 @ sk_C)
% 1.92/2.13        | ((sk_A) = (k1_xboole_0))
% 1.92/2.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.92/2.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.92/2.13        | ~ (v1_funct_1 @ sk_C))),
% 1.92/2.13      inference('sup-', [status(thm)], ['64', '70'])).
% 1.92/2.13  thf('72', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 1.92/2.13      inference('demod', [status(thm)], ['4', '5'])).
% 1.92/2.13  thf('73', plain,
% 1.92/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('74', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.92/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.13  thf('76', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.92/2.13      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 1.92/2.13  thf('77', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.92/2.13      inference('split', [status(esa)], ['9'])).
% 1.92/2.13  thf('78', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.92/2.13      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 1.92/2.13  thf('79', plain, (~ (v2_funct_1 @ sk_C)),
% 1.92/2.13      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 1.92/2.13  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 1.92/2.13      inference('clc', [status(thm)], ['76', '79'])).
% 1.92/2.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.92/2.13  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.92/2.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.92/2.13  thf('82', plain, ((v1_xboole_0 @ sk_C)),
% 1.92/2.13      inference('demod', [status(thm)], ['47', '80', '81'])).
% 1.92/2.13  thf('83', plain, ($false), inference('demod', [status(thm)], ['44', '82'])).
% 1.92/2.13  
% 1.92/2.13  % SZS output end Refutation
% 1.92/2.13  
% 1.92/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
