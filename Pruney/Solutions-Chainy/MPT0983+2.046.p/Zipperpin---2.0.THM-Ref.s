%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.byAKpRo2nq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:08 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 335 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          : 1110 (6634 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('11',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

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

thf('13',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
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

thf('20',plain,(
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

thf('21',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_relat_1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['27','30','31','32','33'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != X18 )
      | ( v2_funct_2 @ X19 @ X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v5_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
      | ( v2_funct_2 @ X19 @ ( k2_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['27','30','31','32','33'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['37','40','41','44'])).

thf('46',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('47',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('49',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['15','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
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

thf('70',plain,(
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

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('83',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['53','84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['50','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.byAKpRo2nq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.59/2.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.59/2.77  % Solved by: fo/fo7.sh
% 2.59/2.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.59/2.77  % done 2265 iterations in 2.318s
% 2.59/2.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.59/2.77  % SZS output start Refutation
% 2.59/2.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.59/2.77  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.59/2.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.59/2.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.59/2.77  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.59/2.77  thf(sk_D_type, type, sk_D: $i).
% 2.59/2.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.59/2.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.59/2.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.59/2.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.59/2.77  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.59/2.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.59/2.77  thf(sk_A_type, type, sk_A: $i).
% 2.59/2.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.59/2.77  thf(sk_B_type, type, sk_B: $i).
% 2.59/2.77  thf(sk_C_type, type, sk_C: $i).
% 2.59/2.77  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.59/2.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.59/2.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.59/2.77  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.59/2.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.59/2.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.59/2.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.59/2.77  thf(l13_xboole_0, axiom,
% 2.59/2.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.59/2.77  thf('0', plain,
% 2.59/2.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.59/2.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.59/2.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.59/2.77  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.59/2.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.59/2.77  thf(dt_k6_partfun1, axiom,
% 2.59/2.77    (![A:$i]:
% 2.59/2.77     ( ( m1_subset_1 @
% 2.59/2.77         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.59/2.77       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.59/2.77  thf('2', plain,
% 2.59/2.77      (![X27 : $i]:
% 2.59/2.77         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 2.59/2.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 2.59/2.77      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.59/2.77  thf(redefinition_k6_partfun1, axiom,
% 2.59/2.77    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.59/2.77  thf('3', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 2.59/2.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.59/2.77  thf('4', plain,
% 2.59/2.77      (![X27 : $i]:
% 2.59/2.77         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 2.59/2.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 2.59/2.77      inference('demod', [status(thm)], ['2', '3'])).
% 2.59/2.77  thf(cc3_relset_1, axiom,
% 2.59/2.77    (![A:$i,B:$i]:
% 2.59/2.77     ( ( v1_xboole_0 @ A ) =>
% 2.59/2.77       ( ![C:$i]:
% 2.59/2.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.59/2.77           ( v1_xboole_0 @ C ) ) ) ))).
% 2.59/2.77  thf('5', plain,
% 2.59/2.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.59/2.77         (~ (v1_xboole_0 @ X8)
% 2.59/2.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 2.59/2.77          | (v1_xboole_0 @ X9))),
% 2.59/2.77      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.59/2.77  thf('6', plain,
% 2.59/2.77      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.59/2.77      inference('sup-', [status(thm)], ['4', '5'])).
% 2.59/2.77  thf('7', plain,
% 2.59/2.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.59/2.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.59/2.77  thf('8', plain,
% 2.59/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 2.59/2.77      inference('sup-', [status(thm)], ['6', '7'])).
% 2.59/2.77  thf('9', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.59/2.77      inference('sup-', [status(thm)], ['1', '8'])).
% 2.59/2.77  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.59/2.77  thf('10', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 2.59/2.77      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.59/2.77  thf('11', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.59/2.77      inference('sup+', [status(thm)], ['9', '10'])).
% 2.59/2.77  thf('12', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.59/2.77      inference('sup+', [status(thm)], ['0', '11'])).
% 2.59/2.77  thf(t29_funct_2, conjecture,
% 2.59/2.77    (![A:$i,B:$i,C:$i]:
% 2.59/2.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.59/2.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.59/2.77       ( ![D:$i]:
% 2.59/2.77         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.59/2.77             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.59/2.77           ( ( r2_relset_1 @
% 2.59/2.77               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.59/2.77               ( k6_partfun1 @ A ) ) =>
% 2.59/2.77             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.59/2.77  thf(zf_stmt_0, negated_conjecture,
% 2.59/2.77    (~( ![A:$i,B:$i,C:$i]:
% 2.59/2.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.59/2.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.59/2.77          ( ![D:$i]:
% 2.59/2.77            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.59/2.77                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.59/2.77              ( ( r2_relset_1 @
% 2.59/2.77                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.59/2.77                  ( k6_partfun1 @ A ) ) =>
% 2.59/2.77                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.59/2.77    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.59/2.77  thf('13', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('14', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.59/2.77      inference('split', [status(esa)], ['13'])).
% 2.59/2.77  thf('15', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.59/2.77      inference('sup-', [status(thm)], ['12', '14'])).
% 2.59/2.77  thf('16', plain,
% 2.59/2.77      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.59/2.77        (k6_partfun1 @ sk_A))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('17', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 2.59/2.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.59/2.77  thf('18', plain,
% 2.59/2.77      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.59/2.77        (k6_relat_1 @ sk_A))),
% 2.59/2.77      inference('demod', [status(thm)], ['16', '17'])).
% 2.59/2.77  thf('19', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(t24_funct_2, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i]:
% 2.59/2.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.59/2.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.59/2.77       ( ![D:$i]:
% 2.59/2.77         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.59/2.77             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.59/2.77           ( ( r2_relset_1 @
% 2.59/2.77               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.59/2.77               ( k6_partfun1 @ B ) ) =>
% 2.59/2.77             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.59/2.77  thf('20', plain,
% 2.59/2.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X29)
% 2.59/2.77          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 2.59/2.77          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.59/2.77          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 2.59/2.77               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 2.59/2.77               (k6_partfun1 @ X30))
% 2.59/2.77          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 2.59/2.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.59/2.77          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 2.59/2.77          | ~ (v1_funct_1 @ X32))),
% 2.59/2.77      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.59/2.77  thf('21', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 2.59/2.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.59/2.77  thf('22', plain,
% 2.59/2.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X29)
% 2.59/2.77          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 2.59/2.77          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.59/2.77          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 2.59/2.77               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 2.59/2.77               (k6_relat_1 @ X30))
% 2.59/2.77          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 2.59/2.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.59/2.77          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 2.59/2.77          | ~ (v1_funct_1 @ X32))),
% 2.59/2.77      inference('demod', [status(thm)], ['20', '21'])).
% 2.59/2.77  thf('23', plain,
% 2.59/2.77      (![X0 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X0)
% 2.59/2.77          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.59/2.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.59/2.77          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.59/2.77          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.59/2.77               (k6_relat_1 @ sk_A))
% 2.59/2.77          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.59/2.77          | ~ (v1_funct_1 @ sk_C))),
% 2.59/2.77      inference('sup-', [status(thm)], ['19', '22'])).
% 2.59/2.77  thf('24', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('26', plain,
% 2.59/2.77      (![X0 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X0)
% 2.59/2.77          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.59/2.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.59/2.77          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.59/2.77          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.59/2.77               (k6_relat_1 @ sk_A)))),
% 2.59/2.77      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.59/2.77  thf('27', plain,
% 2.59/2.77      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.59/2.77        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.59/2.77        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.59/2.77        | ~ (v1_funct_1 @ sk_D))),
% 2.59/2.77      inference('sup-', [status(thm)], ['18', '26'])).
% 2.59/2.77  thf('28', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(redefinition_k2_relset_1, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i]:
% 2.59/2.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.59/2.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.59/2.77  thf('29', plain,
% 2.59/2.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.59/2.77         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 2.59/2.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.59/2.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.59/2.77  thf('30', plain,
% 2.59/2.77      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.59/2.77      inference('sup-', [status(thm)], ['28', '29'])).
% 2.59/2.77  thf('31', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.59/2.77      inference('demod', [status(thm)], ['27', '30', '31', '32', '33'])).
% 2.59/2.77  thf(d3_funct_2, axiom,
% 2.59/2.77    (![A:$i,B:$i]:
% 2.59/2.77     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.59/2.77       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.59/2.77  thf('35', plain,
% 2.59/2.77      (![X18 : $i, X19 : $i]:
% 2.59/2.77         (((k2_relat_1 @ X19) != (X18))
% 2.59/2.77          | (v2_funct_2 @ X19 @ X18)
% 2.59/2.77          | ~ (v5_relat_1 @ X19 @ X18)
% 2.59/2.77          | ~ (v1_relat_1 @ X19))),
% 2.59/2.77      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.59/2.77  thf('36', plain,
% 2.59/2.77      (![X19 : $i]:
% 2.59/2.77         (~ (v1_relat_1 @ X19)
% 2.59/2.77          | ~ (v5_relat_1 @ X19 @ (k2_relat_1 @ X19))
% 2.59/2.77          | (v2_funct_2 @ X19 @ (k2_relat_1 @ X19)))),
% 2.59/2.77      inference('simplify', [status(thm)], ['35'])).
% 2.59/2.77  thf('37', plain,
% 2.59/2.77      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.59/2.77        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.59/2.77        | ~ (v1_relat_1 @ sk_D))),
% 2.59/2.77      inference('sup-', [status(thm)], ['34', '36'])).
% 2.59/2.77  thf('38', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(cc2_relset_1, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i]:
% 2.59/2.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.59/2.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.59/2.77  thf('39', plain,
% 2.59/2.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.59/2.77         ((v5_relat_1 @ X5 @ X7)
% 2.59/2.77          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 2.59/2.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.59/2.77  thf('40', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.59/2.77      inference('sup-', [status(thm)], ['38', '39'])).
% 2.59/2.77  thf('41', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.59/2.77      inference('demod', [status(thm)], ['27', '30', '31', '32', '33'])).
% 2.59/2.77  thf('42', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(cc1_relset_1, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i]:
% 2.59/2.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.59/2.77       ( v1_relat_1 @ C ) ))).
% 2.59/2.77  thf('43', plain,
% 2.59/2.77      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.59/2.77         ((v1_relat_1 @ X2)
% 2.59/2.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 2.59/2.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.59/2.77  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 2.59/2.77      inference('sup-', [status(thm)], ['42', '43'])).
% 2.59/2.77  thf('45', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.59/2.77      inference('demod', [status(thm)], ['37', '40', '41', '44'])).
% 2.59/2.77  thf('46', plain,
% 2.59/2.77      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.59/2.77      inference('split', [status(esa)], ['13'])).
% 2.59/2.77  thf('47', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.59/2.77      inference('sup-', [status(thm)], ['45', '46'])).
% 2.59/2.77  thf('48', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.59/2.77      inference('split', [status(esa)], ['13'])).
% 2.59/2.77  thf('49', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.59/2.77      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 2.59/2.77  thf('50', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.59/2.77      inference('simpl_trail', [status(thm)], ['15', '49'])).
% 2.59/2.77  thf('51', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('52', plain,
% 2.59/2.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.59/2.77         (~ (v1_xboole_0 @ X8)
% 2.59/2.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 2.59/2.77          | (v1_xboole_0 @ X9))),
% 2.59/2.77      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.59/2.77  thf('53', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.59/2.77      inference('sup-', [status(thm)], ['51', '52'])).
% 2.59/2.77  thf('54', plain,
% 2.59/2.77      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.59/2.77        (k6_relat_1 @ sk_A))),
% 2.59/2.77      inference('demod', [status(thm)], ['16', '17'])).
% 2.59/2.77  thf('55', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('56', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(dt_k1_partfun1, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.59/2.77     ( ( ( v1_funct_1 @ E ) & 
% 2.59/2.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.59/2.77         ( v1_funct_1 @ F ) & 
% 2.59/2.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.59/2.77       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.59/2.77         ( m1_subset_1 @
% 2.59/2.77           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.59/2.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.59/2.77  thf('57', plain,
% 2.59/2.77      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.59/2.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.59/2.77          | ~ (v1_funct_1 @ X20)
% 2.59/2.77          | ~ (v1_funct_1 @ X23)
% 2.59/2.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.59/2.77          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 2.59/2.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 2.59/2.77      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.59/2.77  thf('58', plain,
% 2.59/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.77         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.59/2.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.59/2.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.59/2.77          | ~ (v1_funct_1 @ X1)
% 2.59/2.77          | ~ (v1_funct_1 @ sk_C))),
% 2.59/2.77      inference('sup-', [status(thm)], ['56', '57'])).
% 2.59/2.77  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('60', plain,
% 2.59/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.77         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.59/2.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.59/2.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.59/2.77          | ~ (v1_funct_1 @ X1))),
% 2.59/2.77      inference('demod', [status(thm)], ['58', '59'])).
% 2.59/2.77  thf('61', plain,
% 2.59/2.77      ((~ (v1_funct_1 @ sk_D)
% 2.59/2.77        | (m1_subset_1 @ 
% 2.59/2.77           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.59/2.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.59/2.77      inference('sup-', [status(thm)], ['55', '60'])).
% 2.59/2.77  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('63', plain,
% 2.59/2.77      ((m1_subset_1 @ 
% 2.59/2.77        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.59/2.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.59/2.77      inference('demod', [status(thm)], ['61', '62'])).
% 2.59/2.77  thf(redefinition_r2_relset_1, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i,D:$i]:
% 2.59/2.77     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.59/2.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.59/2.77       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.59/2.77  thf('64', plain,
% 2.59/2.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.59/2.77         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 2.59/2.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 2.59/2.77          | ((X14) = (X17))
% 2.59/2.77          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 2.59/2.77      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.59/2.77  thf('65', plain,
% 2.59/2.77      (![X0 : $i]:
% 2.59/2.77         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.59/2.77             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.59/2.77          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.59/2.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.59/2.77      inference('sup-', [status(thm)], ['63', '64'])).
% 2.59/2.77  thf('66', plain,
% 2.59/2.77      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.59/2.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.59/2.77        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.59/2.77            = (k6_relat_1 @ sk_A)))),
% 2.59/2.77      inference('sup-', [status(thm)], ['54', '65'])).
% 2.59/2.77  thf('67', plain,
% 2.59/2.77      (![X27 : $i]:
% 2.59/2.77         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 2.59/2.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 2.59/2.77      inference('demod', [status(thm)], ['2', '3'])).
% 2.59/2.77  thf('68', plain,
% 2.59/2.77      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.59/2.77         = (k6_relat_1 @ sk_A))),
% 2.59/2.77      inference('demod', [status(thm)], ['66', '67'])).
% 2.59/2.77  thf('69', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf(t26_funct_2, axiom,
% 2.59/2.77    (![A:$i,B:$i,C:$i,D:$i]:
% 2.59/2.77     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.59/2.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.59/2.77       ( ![E:$i]:
% 2.59/2.77         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.59/2.77             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.59/2.77           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.59/2.77             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.59/2.77               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.59/2.77  thf('70', plain,
% 2.59/2.77      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X33)
% 2.59/2.77          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.59/2.77          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.59/2.77          | ~ (v2_funct_1 @ (k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33))
% 2.59/2.77          | (v2_funct_1 @ X37)
% 2.59/2.77          | ((X35) = (k1_xboole_0))
% 2.59/2.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 2.59/2.77          | ~ (v1_funct_2 @ X37 @ X36 @ X34)
% 2.59/2.77          | ~ (v1_funct_1 @ X37))),
% 2.59/2.77      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.59/2.77  thf('71', plain,
% 2.59/2.77      (![X0 : $i, X1 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X0)
% 2.59/2.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.59/2.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.59/2.77          | ((sk_A) = (k1_xboole_0))
% 2.59/2.77          | (v2_funct_1 @ X0)
% 2.59/2.77          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.59/2.77          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.59/2.77          | ~ (v1_funct_1 @ sk_D))),
% 2.59/2.77      inference('sup-', [status(thm)], ['69', '70'])).
% 2.59/2.77  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('74', plain,
% 2.59/2.77      (![X0 : $i, X1 : $i]:
% 2.59/2.77         (~ (v1_funct_1 @ X0)
% 2.59/2.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.59/2.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.59/2.77          | ((sk_A) = (k1_xboole_0))
% 2.59/2.77          | (v2_funct_1 @ X0)
% 2.59/2.77          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.59/2.77      inference('demod', [status(thm)], ['71', '72', '73'])).
% 2.59/2.77  thf('75', plain,
% 2.59/2.77      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.59/2.77        | (v2_funct_1 @ sk_C)
% 2.59/2.77        | ((sk_A) = (k1_xboole_0))
% 2.59/2.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.59/2.77        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.59/2.77        | ~ (v1_funct_1 @ sk_C))),
% 2.59/2.77      inference('sup-', [status(thm)], ['68', '74'])).
% 2.59/2.77  thf('76', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 2.59/2.77      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.59/2.77  thf('77', plain,
% 2.59/2.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 2.59/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.77  thf('80', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.59/2.77      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 2.59/2.77  thf('81', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.59/2.77      inference('split', [status(esa)], ['13'])).
% 2.59/2.77  thf('82', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.59/2.77      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 2.59/2.77  thf('83', plain, (~ (v2_funct_1 @ sk_C)),
% 2.59/2.77      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 2.59/2.77  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 2.59/2.77      inference('clc', [status(thm)], ['80', '83'])).
% 2.59/2.77  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.59/2.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.59/2.77  thf('86', plain, ((v1_xboole_0 @ sk_C)),
% 2.59/2.77      inference('demod', [status(thm)], ['53', '84', '85'])).
% 2.59/2.77  thf('87', plain, ($false), inference('demod', [status(thm)], ['50', '86'])).
% 2.59/2.77  
% 2.59/2.77  % SZS output end Refutation
% 2.59/2.77  
% 2.59/2.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
