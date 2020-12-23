%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZIkWAtapdp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:05 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  248 (1294 expanded)
%              Number of leaves         :   45 ( 399 expanded)
%              Depth                    :   21
%              Number of atoms          : 2155 (27787 expanded)
%              Number of equality atoms :  113 ( 779 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','50'])).

thf('52',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('60',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','57','58','59'])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('66',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('80',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','73','80','81','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('106',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('116',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118'])).

thf('120',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('122',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('123',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('129',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('130',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('135',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('136',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('137',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('141',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('142',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('144',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('145',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('147',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['140','160'])).

thf('162',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('167',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('168',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('169',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','167','168','169'])).

thf('171',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('172',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('173',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('174',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','170','171','177'])).

thf('179',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('181',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('182',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','167','168','169'])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('185',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','185'])).

thf('187',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','110','120','127','179','186'])).

thf('188',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['60','92','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('192',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('200',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['189','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZIkWAtapdp
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.82/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.06  % Solved by: fo/fo7.sh
% 0.82/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.06  % done 516 iterations in 0.543s
% 0.82/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.06  % SZS output start Refutation
% 0.82/1.06  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.82/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.06  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.82/1.06  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.82/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.82/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.06  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.82/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.82/1.06  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.82/1.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.82/1.06  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.82/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.82/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.06  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.82/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.06  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.82/1.06  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.82/1.06  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.82/1.06  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.82/1.06  thf(d3_struct_0, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.82/1.06  thf('0', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('1', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf(t64_tops_2, conjecture,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( l1_struct_0 @ A ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.82/1.06           ( ![C:$i]:
% 0.82/1.06             ( ( ( v1_funct_1 @ C ) & 
% 0.82/1.06                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.82/1.06                 ( m1_subset_1 @
% 0.82/1.06                   C @ 
% 0.82/1.06                   ( k1_zfmisc_1 @
% 0.82/1.06                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.82/1.06               ( ( ( ( k2_relset_1 @
% 0.82/1.06                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.82/1.06                     ( k2_struct_0 @ B ) ) & 
% 0.82/1.06                   ( v2_funct_1 @ C ) ) =>
% 0.82/1.06                 ( r2_funct_2 @
% 0.82/1.06                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.82/1.06                   ( k2_tops_2 @
% 0.82/1.06                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.82/1.06                     ( k2_tops_2 @
% 0.82/1.06                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.82/1.06                   C ) ) ) ) ) ) ))).
% 0.82/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.06    (~( ![A:$i]:
% 0.82/1.06        ( ( l1_struct_0 @ A ) =>
% 0.82/1.06          ( ![B:$i]:
% 0.82/1.06            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.82/1.06              ( ![C:$i]:
% 0.82/1.06                ( ( ( v1_funct_1 @ C ) & 
% 0.82/1.06                    ( v1_funct_2 @
% 0.82/1.06                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.82/1.06                    ( m1_subset_1 @
% 0.82/1.06                      C @ 
% 0.82/1.06                      ( k1_zfmisc_1 @
% 0.82/1.06                        ( k2_zfmisc_1 @
% 0.82/1.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.82/1.06                  ( ( ( ( k2_relset_1 @
% 0.82/1.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.82/1.06                        ( k2_struct_0 @ B ) ) & 
% 0.82/1.06                      ( v2_funct_1 @ C ) ) =>
% 0.82/1.06                    ( r2_funct_2 @
% 0.82/1.06                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.82/1.06                      ( k2_tops_2 @
% 0.82/1.06                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.82/1.06                        ( k2_tops_2 @
% 0.82/1.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.82/1.06                      C ) ) ) ) ) ) ) )),
% 0.82/1.06    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.82/1.06  thf('2', plain,
% 0.82/1.06      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06          sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('3', plain,
% 0.82/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06           sk_C)
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.82/1.06  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('5', plain,
% 0.82/1.06      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06          sk_C)),
% 0.82/1.06      inference('demod', [status(thm)], ['3', '4'])).
% 0.82/1.06  thf('6', plain,
% 0.82/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06           sk_C)
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['0', '5'])).
% 0.82/1.06  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('8', plain,
% 0.82/1.06      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06          sk_C)),
% 0.82/1.06      inference('demod', [status(thm)], ['6', '7'])).
% 0.82/1.06  thf('9', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(cc5_funct_2, axiom,
% 0.82/1.06    (![A:$i,B:$i]:
% 0.82/1.06     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.82/1.06       ( ![C:$i]:
% 0.82/1.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.82/1.06             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('10', plain,
% 0.82/1.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.82/1.06          | (v1_partfun1 @ X18 @ X19)
% 0.82/1.06          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.82/1.06          | ~ (v1_funct_1 @ X18)
% 0.82/1.06          | (v1_xboole_0 @ X20))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.82/1.06  thf('11', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.06  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('13', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('14', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.82/1.06  thf(d4_partfun1, axiom,
% 0.82/1.06    (![A:$i,B:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.82/1.06       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.82/1.06  thf('15', plain,
% 0.82/1.06      (![X21 : $i, X22 : $i]:
% 0.82/1.06         (~ (v1_partfun1 @ X22 @ X21)
% 0.82/1.06          | ((k1_relat_1 @ X22) = (X21))
% 0.82/1.06          | ~ (v4_relat_1 @ X22 @ X21)
% 0.82/1.06          | ~ (v1_relat_1 @ X22))),
% 0.82/1.06      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.82/1.06  thf('16', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('17', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(cc1_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( v1_relat_1 @ C ) ))).
% 0.82/1.06  thf('18', plain,
% 0.82/1.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.06         ((v1_relat_1 @ X9)
% 0.82/1.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.82/1.06  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('20', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(cc2_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.82/1.06  thf('21', plain,
% 0.82/1.06      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         ((v4_relat_1 @ X12 @ X13)
% 0.82/1.06          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.82/1.06  thf('22', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.82/1.06  thf('23', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.82/1.06  thf('24', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('25', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('26', plain,
% 0.82/1.06      (((m1_subset_1 @ sk_C @ 
% 0.82/1.06         (k1_zfmisc_1 @ 
% 0.82/1.06          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup+', [status(thm)], ['24', '25'])).
% 0.82/1.06  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('28', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('29', plain,
% 0.82/1.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.82/1.06          | (v1_partfun1 @ X18 @ X19)
% 0.82/1.06          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.82/1.06          | ~ (v1_funct_1 @ X18)
% 0.82/1.06          | (v1_xboole_0 @ X20))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.82/1.06  thf('30', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['28', '29'])).
% 0.82/1.06  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('32', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('33', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('34', plain,
% 0.82/1.06      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup+', [status(thm)], ['32', '33'])).
% 0.82/1.06  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('36', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.06  thf('37', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['30', '31', '36'])).
% 0.82/1.06  thf('38', plain,
% 0.82/1.06      (![X21 : $i, X22 : $i]:
% 0.82/1.06         (~ (v1_partfun1 @ X22 @ X21)
% 0.82/1.06          | ((k1_relat_1 @ X22) = (X21))
% 0.82/1.06          | ~ (v4_relat_1 @ X22 @ X21)
% 0.82/1.06          | ~ (v1_relat_1 @ X22))),
% 0.82/1.06      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.82/1.06  thf('39', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.82/1.06        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['37', '38'])).
% 0.82/1.06  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('41', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('42', plain,
% 0.82/1.06      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         ((v4_relat_1 @ X12 @ X13)
% 0.82/1.06          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.82/1.06  thf('43', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['41', '42'])).
% 0.82/1.06  thf('44', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.82/1.06  thf(fc2_struct_0, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.82/1.06       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/1.06  thf('45', plain,
% 0.82/1.06      (![X31 : $i]:
% 0.82/1.06         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.82/1.06          | ~ (l1_struct_0 @ X31)
% 0.82/1.06          | (v2_struct_0 @ X31))),
% 0.82/1.06      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.82/1.06  thf('46', plain,
% 0.82/1.06      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.06  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('48', plain,
% 0.82/1.06      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['46', '47'])).
% 0.82/1.06  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('50', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['48', '49'])).
% 0.82/1.06  thf('51', plain,
% 0.82/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.82/1.06        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['23', '50'])).
% 0.82/1.06  thf('52', plain,
% 0.82/1.06      (![X31 : $i]:
% 0.82/1.06         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.82/1.06          | ~ (l1_struct_0 @ X31)
% 0.82/1.06          | (v2_struct_0 @ X31))),
% 0.82/1.06      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.82/1.06  thf('53', plain,
% 0.82/1.06      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['51', '52'])).
% 0.82/1.06  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('55', plain,
% 0.82/1.06      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['53', '54'])).
% 0.82/1.06  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['55', '56'])).
% 0.82/1.06  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['55', '56'])).
% 0.82/1.06  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['55', '56'])).
% 0.82/1.06  thf('60', plain,
% 0.82/1.06      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.82/1.06          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.82/1.06          sk_C)),
% 0.82/1.06      inference('demod', [status(thm)], ['8', '57', '58', '59'])).
% 0.82/1.06  thf('61', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('62', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('63', plain,
% 0.82/1.06      (((m1_subset_1 @ sk_C @ 
% 0.82/1.06         (k1_zfmisc_1 @ 
% 0.82/1.06          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup+', [status(thm)], ['61', '62'])).
% 0.82/1.06  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('65', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['63', '64'])).
% 0.82/1.06  thf(d4_tops_2, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.82/1.06         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.82/1.06  thf('66', plain,
% 0.82/1.06      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.82/1.06         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.82/1.06          | ~ (v2_funct_1 @ X34)
% 0.82/1.06          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.82/1.06          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.82/1.06          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.82/1.06          | ~ (v1_funct_1 @ X34))),
% 0.82/1.06      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.82/1.06  thf('67', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.82/1.06        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06            = (k2_funct_1 @ sk_C))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C)
% 0.82/1.06        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06            != (k2_struct_0 @ sk_B)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['65', '66'])).
% 0.82/1.06  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('69', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('70', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.06  thf('71', plain,
% 0.82/1.06      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup+', [status(thm)], ['69', '70'])).
% 0.82/1.06  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('73', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['71', '72'])).
% 0.82/1.06  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(d9_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.82/1.06  thf('75', plain,
% 0.82/1.06      (![X1 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X1)
% 0.82/1.06          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.82/1.06          | ~ (v1_funct_1 @ X1)
% 0.82/1.06          | ~ (v1_relat_1 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.82/1.06  thf('76', plain,
% 0.82/1.06      ((~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['74', '75'])).
% 0.82/1.06  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('78', plain,
% 0.82/1.06      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)], ['76', '77'])).
% 0.82/1.06  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('80', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('82', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('83', plain,
% 0.82/1.06      (![X30 : $i]:
% 0.82/1.06         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.82/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/1.06  thf('84', plain,
% 0.82/1.06      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('85', plain,
% 0.82/1.06      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06          = (k2_struct_0 @ sk_B))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup+', [status(thm)], ['83', '84'])).
% 0.82/1.06  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('87', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['85', '86'])).
% 0.82/1.06  thf('88', plain,
% 0.82/1.06      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06          = (k2_struct_0 @ sk_B))
% 0.82/1.06        | ~ (l1_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup+', [status(thm)], ['82', '87'])).
% 0.82/1.06  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('90', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['88', '89'])).
% 0.82/1.06  thf('91', plain,
% 0.82/1.06      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06          = (k4_relat_1 @ sk_C))
% 0.82/1.06        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.82/1.06      inference('demod', [status(thm)], ['67', '68', '73', '80', '81', '90'])).
% 0.82/1.06  thf('92', plain,
% 0.82/1.06      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('simplify', [status(thm)], ['91'])).
% 0.82/1.06  thf('93', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['63', '64'])).
% 0.82/1.06  thf(t31_funct_2, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.82/1.06         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.82/1.06           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.82/1.06           ( m1_subset_1 @
% 0.82/1.06             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('94', plain,
% 0.82/1.06      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X27)
% 0.82/1.06          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.82/1.06          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.82/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.82/1.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.82/1.06          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.82/1.06          | ~ (v1_funct_1 @ X27))),
% 0.82/1.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.06  thf('95', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.82/1.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.06           (k1_zfmisc_1 @ 
% 0.82/1.06            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.82/1.06        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06            != (k2_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['93', '94'])).
% 0.82/1.06  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('97', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['71', '72'])).
% 0.82/1.06  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('99', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['88', '89'])).
% 0.82/1.06  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('101', plain,
% 0.82/1.06      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.82/1.06         (k1_zfmisc_1 @ 
% 0.82/1.06          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.82/1.06        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.82/1.06      inference('demod', [status(thm)], ['95', '96', '97', '98', '99', '100'])).
% 0.82/1.06  thf('102', plain,
% 0.82/1.06      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.82/1.06      inference('simplify', [status(thm)], ['101'])).
% 0.82/1.06  thf('103', plain,
% 0.82/1.06      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.82/1.06         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.82/1.06          | ~ (v2_funct_1 @ X34)
% 0.82/1.06          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.82/1.06          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.82/1.06          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.82/1.06          | ~ (v1_funct_1 @ X34))),
% 0.82/1.06      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.82/1.06  thf('104', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.82/1.06             (k2_struct_0 @ sk_A))
% 0.82/1.06        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.82/1.06        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06            (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['102', '103'])).
% 0.82/1.06  thf('105', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf(dt_k2_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.82/1.06         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.82/1.06  thf('106', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('107', plain,
% 0.82/1.06      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup+', [status(thm)], ['105', '106'])).
% 0.82/1.06  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('110', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.82/1.06  thf('111', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['63', '64'])).
% 0.82/1.06  thf('112', plain,
% 0.82/1.06      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X27)
% 0.82/1.06          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.82/1.06          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.82/1.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.82/1.06          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.82/1.06          | ~ (v1_funct_1 @ X27))),
% 0.82/1.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.06  thf('113', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.82/1.06        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.82/1.06           (k2_struct_0 @ sk_A))
% 0.82/1.06        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06            != (k2_struct_0 @ sk_B))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['111', '112'])).
% 0.82/1.06  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('115', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['71', '72'])).
% 0.82/1.06  thf('116', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('117', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.82/1.06         = (k2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['88', '89'])).
% 0.82/1.06  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('119', plain,
% 0.82/1.06      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.82/1.06         (k2_struct_0 @ sk_A))
% 0.82/1.06        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['113', '114', '115', '116', '117', '118'])).
% 0.82/1.06  thf('120', plain,
% 0.82/1.06      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.82/1.06        (k2_struct_0 @ sk_A))),
% 0.82/1.06      inference('simplify', [status(thm)], ['119'])).
% 0.82/1.06  thf('121', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf(t65_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.82/1.06  thf('122', plain,
% 0.82/1.06      (![X8 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X8)
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ X8)) = (X8))
% 0.82/1.06          | ~ (v1_funct_1 @ X8)
% 0.82/1.06          | ~ (v1_relat_1 @ X8))),
% 0.82/1.06      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.82/1.06  thf('123', plain,
% 0.82/1.06      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup+', [status(thm)], ['121', '122'])).
% 0.82/1.06  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('127', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.82/1.06  thf('128', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf(t61_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ( v2_funct_1 @ A ) =>
% 0.82/1.06         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.82/1.06             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.82/1.06           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.82/1.06             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('129', plain,
% 0.82/1.06      (![X7 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X7)
% 0.82/1.06          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 0.82/1.06              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.82/1.06          | ~ (v1_funct_1 @ X7)
% 0.82/1.06          | ~ (v1_relat_1 @ X7))),
% 0.82/1.06      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.82/1.06  thf('130', plain,
% 0.82/1.06      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.82/1.06          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup+', [status(thm)], ['128', '129'])).
% 0.82/1.06  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('134', plain,
% 0.82/1.06      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.82/1.06         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.82/1.06  thf(t48_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.82/1.06           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.82/1.06               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.82/1.06             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('135', plain,
% 0.82/1.06      (![X5 : $i, X6 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X5)
% 0.82/1.06          | ~ (v1_funct_1 @ X5)
% 0.82/1.06          | (v2_funct_1 @ X5)
% 0.82/1.06          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.82/1.06          | ~ (v2_funct_1 @ (k5_relat_1 @ X5 @ X6))
% 0.82/1.06          | ~ (v1_funct_1 @ X6)
% 0.82/1.06          | ~ (v1_relat_1 @ X6))),
% 0.82/1.06      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.82/1.06  thf('136', plain,
% 0.82/1.06      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.82/1.06        | (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['134', '135'])).
% 0.82/1.06  thf(fc4_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.82/1.06       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.82/1.06  thf('137', plain, (![X4 : $i]: (v2_funct_1 @ (k6_relat_1 @ X4))),
% 0.82/1.06      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.82/1.06  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('140', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('141', plain,
% 0.82/1.06      (![X8 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X8)
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ X8)) = (X8))
% 0.82/1.06          | ~ (v1_funct_1 @ X8)
% 0.82/1.06          | ~ (v1_relat_1 @ X8))),
% 0.82/1.06      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.82/1.06  thf('142', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('143', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('144', plain,
% 0.82/1.06      (![X8 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X8)
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ X8)) = (X8))
% 0.82/1.06          | ~ (v1_funct_1 @ X8)
% 0.82/1.06          | ~ (v1_relat_1 @ X8))),
% 0.82/1.06      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.82/1.06  thf('145', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('146', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('147', plain,
% 0.82/1.06      (![X1 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X1)
% 0.82/1.06          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.82/1.06          | ~ (v1_funct_1 @ X1)
% 0.82/1.06          | ~ (v1_relat_1 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.82/1.06  thf('148', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['146', '147'])).
% 0.82/1.06  thf('149', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['145', '148'])).
% 0.82/1.06  thf('150', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('simplify', [status(thm)], ['149'])).
% 0.82/1.06  thf('151', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['144', '150'])).
% 0.82/1.06  thf('152', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.82/1.06          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0))),
% 0.82/1.06      inference('simplify', [status(thm)], ['151'])).
% 0.82/1.06  thf('153', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['143', '152'])).
% 0.82/1.06  thf('154', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('simplify', [status(thm)], ['153'])).
% 0.82/1.06  thf('155', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['142', '154'])).
% 0.82/1.06  thf('156', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('simplify', [status(thm)], ['155'])).
% 0.82/1.06  thf('157', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k2_funct_1 @ X0) = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0))),
% 0.82/1.06      inference('sup+', [status(thm)], ['141', '156'])).
% 0.82/1.06  thf('158', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ((k2_funct_1 @ X0)
% 0.82/1.06              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.82/1.06      inference('simplify', [status(thm)], ['157'])).
% 0.82/1.06  thf(t37_relat_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( v1_relat_1 @ A ) =>
% 0.82/1.06       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.82/1.06         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.82/1.06  thf('159', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.82/1.06  thf('160', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06          | ~ (v1_relat_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v2_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.82/1.06      inference('sup+', [status(thm)], ['158', '159'])).
% 0.82/1.06  thf('161', plain,
% 0.82/1.06      ((~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.82/1.06            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['140', '160'])).
% 0.82/1.06  thf('162', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.82/1.06  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('167', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('168', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.82/1.06  thf('169', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('170', plain,
% 0.82/1.06      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['161', '162', '163', '164', '165', '166', '167', '168', '169'])).
% 0.82/1.06  thf('171', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.82/1.06  thf('172', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('173', plain,
% 0.82/1.06      (![X2 : $i]:
% 0.82/1.06         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.06  thf('174', plain,
% 0.82/1.06      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup+', [status(thm)], ['172', '173'])).
% 0.82/1.06  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('177', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.82/1.06  thf('178', plain,
% 0.82/1.06      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.82/1.06        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['136', '137', '138', '139', '170', '171', '177'])).
% 0.82/1.06  thf('179', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.82/1.06      inference('simplify', [status(thm)], ['178'])).
% 0.82/1.06  thf('180', plain,
% 0.82/1.06      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.82/1.06      inference('simplify', [status(thm)], ['101'])).
% 0.82/1.06  thf(redefinition_k2_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.82/1.06  thf('181', plain,
% 0.82/1.06      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.06         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.82/1.06          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.82/1.06  thf('182', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['180', '181'])).
% 0.82/1.06  thf('183', plain,
% 0.82/1.06      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['161', '162', '163', '164', '165', '166', '167', '168', '169'])).
% 0.82/1.06  thf('184', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['48', '49'])).
% 0.82/1.06  thf('185', plain,
% 0.82/1.06      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)], ['183', '184'])).
% 0.82/1.06  thf('186', plain,
% 0.82/1.06      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06         (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['182', '185'])).
% 0.82/1.06  thf('187', plain,
% 0.82/1.06      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.82/1.06        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['104', '110', '120', '127', '179', '186'])).
% 0.82/1.06  thf('188', plain,
% 0.82/1.06      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.82/1.06         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.82/1.06      inference('simplify', [status(thm)], ['187'])).
% 0.82/1.06  thf('189', plain,
% 0.82/1.06      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.82/1.06          sk_C)),
% 0.82/1.06      inference('demod', [status(thm)], ['60', '92', '188'])).
% 0.82/1.06  thf('190', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('191', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ 
% 0.82/1.06        (k1_zfmisc_1 @ 
% 0.82/1.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.82/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf(reflexivity_r2_funct_2, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.06         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.82/1.06  thf('192', plain,
% 0.82/1.06      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.82/1.06         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.82/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.82/1.06          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.82/1.06          | ~ (v1_funct_1 @ X25)
% 0.82/1.06          | ~ (v1_funct_1 @ X26)
% 0.82/1.06          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.82/1.06          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.82/1.06      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.82/1.06  thf('193', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X0 @ 
% 0.82/1.06             (k1_zfmisc_1 @ 
% 0.82/1.06              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.82/1.06          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.82/1.06             sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['191', '192'])).
% 0.82/1.06  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('195', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.06  thf('196', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X0 @ 
% 0.82/1.06             (k1_zfmisc_1 @ 
% 0.82/1.06              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.82/1.06          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.82/1.06             sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['193', '194', '195'])).
% 0.82/1.06  thf('197', plain,
% 0.82/1.06      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['190', '196'])).
% 0.82/1.06  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('199', plain,
% 0.82/1.06      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['34', '35'])).
% 0.82/1.06  thf('200', plain,
% 0.82/1.06      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.82/1.06      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.82/1.06  thf('201', plain, ($false), inference('demod', [status(thm)], ['189', '200'])).
% 0.82/1.06  
% 0.82/1.06  % SZS output end Refutation
% 0.82/1.06  
% 0.82/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
