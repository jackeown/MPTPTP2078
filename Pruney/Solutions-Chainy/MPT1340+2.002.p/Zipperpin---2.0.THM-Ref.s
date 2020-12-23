%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8y3fVOc7DN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:05 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  238 (1451 expanded)
%              Number of leaves         :   41 ( 448 expanded)
%              Depth                    :   23
%              Number of atoms          : 2107 (31818 expanded)
%              Number of equality atoms :  106 ( 837 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','73','79','80','89'])).

thf('91',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('97',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('98',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('105',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('112',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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
    inference(demod,[status(thm)],['76','77','78'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

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
    inference(demod,[status(thm)],['76','77','78'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('122',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    inference(demod,[status(thm)],['76','77','78'])).

thf('129',plain,(
    ! [X7: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('130',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
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

thf('134',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('136',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('138',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('139',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('140',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('141',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('143',plain,(
    ! [X7: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('144',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('145',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('146',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['141','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['140','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('158',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('159',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('160',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('161',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('162',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('163',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('164',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['139','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('168',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('169',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('170',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('173',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('175',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','175'])).

thf('177',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','110','120','127','134','176'])).

thf('178',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['60','91','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('182',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('188',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('189',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','190'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('194',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['179','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8y3fVOc7DN
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.71  % Solved by: fo/fo7.sh
% 0.49/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.71  % done 519 iterations in 0.256s
% 0.49/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.71  % SZS output start Refutation
% 0.49/0.71  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.71  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.49/0.71  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.49/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.71  thf(d3_struct_0, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.71  thf('0', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('1', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf(t64_tops_2, conjecture,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( l1_struct_0 @ A ) =>
% 0.49/0.71       ( ![B:$i]:
% 0.49/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.71           ( ![C:$i]:
% 0.49/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.71                 ( m1_subset_1 @
% 0.49/0.71                   C @ 
% 0.49/0.71                   ( k1_zfmisc_1 @
% 0.49/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.71               ( ( ( ( k2_relset_1 @
% 0.49/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.49/0.71                   ( v2_funct_1 @ C ) ) =>
% 0.49/0.71                 ( r2_funct_2 @
% 0.49/0.71                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.71                   ( k2_tops_2 @
% 0.49/0.71                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.71                     ( k2_tops_2 @
% 0.49/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.71                   C ) ) ) ) ) ) ))).
% 0.49/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.71    (~( ![A:$i]:
% 0.49/0.71        ( ( l1_struct_0 @ A ) =>
% 0.49/0.71          ( ![B:$i]:
% 0.49/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.71              ( ![C:$i]:
% 0.49/0.71                ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.71                    ( v1_funct_2 @
% 0.49/0.71                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.71                    ( m1_subset_1 @
% 0.49/0.71                      C @ 
% 0.49/0.71                      ( k1_zfmisc_1 @
% 0.49/0.71                        ( k2_zfmisc_1 @
% 0.49/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.71                  ( ( ( ( k2_relset_1 @
% 0.49/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.49/0.71                      ( v2_funct_1 @ C ) ) =>
% 0.49/0.71                    ( r2_funct_2 @
% 0.49/0.71                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.71                      ( k2_tops_2 @
% 0.49/0.71                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.71                        ( k2_tops_2 @
% 0.49/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.71                      C ) ) ) ) ) ) ) )),
% 0.49/0.71    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.49/0.71  thf('2', plain,
% 0.49/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71          sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('3', plain,
% 0.49/0.71      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.71            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71           sk_C)
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.71  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('5', plain,
% 0.49/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71          sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.49/0.71  thf('6', plain,
% 0.49/0.71      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.71            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71           sk_C)
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup-', [status(thm)], ['0', '5'])).
% 0.49/0.71  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('8', plain,
% 0.49/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71          sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.71  thf('9', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(cc5_funct_2, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.71       ( ![C:$i]:
% 0.49/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.71  thf('10', plain,
% 0.49/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.49/0.71          | (v1_partfun1 @ X20 @ X21)
% 0.49/0.71          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.49/0.71          | ~ (v1_funct_1 @ X20)
% 0.49/0.71          | (v1_xboole_0 @ X22))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.71  thf('11', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.71  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('13', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('14', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.49/0.71  thf(d4_partfun1, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.49/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.49/0.71  thf('15', plain,
% 0.49/0.71      (![X23 : $i, X24 : $i]:
% 0.49/0.71         (~ (v1_partfun1 @ X24 @ X23)
% 0.49/0.71          | ((k1_relat_1 @ X24) = (X23))
% 0.49/0.71          | ~ (v4_relat_1 @ X24 @ X23)
% 0.49/0.71          | ~ (v1_relat_1 @ X24))),
% 0.49/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.71  thf('16', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.49/0.71        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.49/0.71  thf('17', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(cc1_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( v1_relat_1 @ C ) ))).
% 0.49/0.71  thf('18', plain,
% 0.49/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.71         ((v1_relat_1 @ X11)
% 0.49/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.71  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('20', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(cc2_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.71  thf('21', plain,
% 0.49/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.71         ((v4_relat_1 @ X14 @ X15)
% 0.49/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.71  thf('22', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.71  thf('23', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.49/0.71  thf('24', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('25', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('26', plain,
% 0.49/0.71      (((m1_subset_1 @ sk_C @ 
% 0.49/0.71         (k1_zfmisc_1 @ 
% 0.49/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.49/0.71  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('28', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf('29', plain,
% 0.49/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.49/0.71          | (v1_partfun1 @ X20 @ X21)
% 0.49/0.71          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.49/0.71          | ~ (v1_funct_1 @ X20)
% 0.49/0.71          | (v1_xboole_0 @ X22))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.71  thf('30', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.71  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('32', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('33', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('34', plain,
% 0.49/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.71      inference('sup+', [status(thm)], ['32', '33'])).
% 0.49/0.71  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('36', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.71  thf('37', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['30', '31', '36'])).
% 0.49/0.71  thf('38', plain,
% 0.49/0.71      (![X23 : $i, X24 : $i]:
% 0.49/0.71         (~ (v1_partfun1 @ X24 @ X23)
% 0.49/0.71          | ((k1_relat_1 @ X24) = (X23))
% 0.49/0.71          | ~ (v4_relat_1 @ X24 @ X23)
% 0.49/0.71          | ~ (v1_relat_1 @ X24))),
% 0.49/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.71  thf('39', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.49/0.71        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.71  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('41', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf('42', plain,
% 0.49/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.71         ((v4_relat_1 @ X14 @ X15)
% 0.49/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.71  thf('43', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.71  thf('44', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.49/0.71  thf(fc2_struct_0, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.49/0.71       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.71  thf('45', plain,
% 0.49/0.71      (![X33 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.49/0.71          | ~ (l1_struct_0 @ X33)
% 0.49/0.71          | (v2_struct_0 @ X33))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.49/0.71  thf('46', plain,
% 0.49/0.71      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.49/0.71        | (v2_struct_0 @ sk_B)
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.71  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('48', plain,
% 0.49/0.71      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['46', '47'])).
% 0.49/0.71  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('50', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['48', '49'])).
% 0.49/0.71  thf('51', plain,
% 0.49/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.49/0.71        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['23', '50'])).
% 0.49/0.71  thf('52', plain,
% 0.49/0.71      (![X33 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.49/0.71          | ~ (l1_struct_0 @ X33)
% 0.49/0.71          | (v2_struct_0 @ X33))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.49/0.71  thf('53', plain,
% 0.49/0.71      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.49/0.71        | (v2_struct_0 @ sk_B)
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.71  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('55', plain,
% 0.49/0.71      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['53', '54'])).
% 0.49/0.71  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('60', plain,
% 0.49/0.71      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.71          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.71          sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['8', '57', '58', '59'])).
% 0.49/0.71  thf('61', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('62', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf('63', plain,
% 0.49/0.71      (((m1_subset_1 @ sk_C @ 
% 0.49/0.71         (k1_zfmisc_1 @ 
% 0.49/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup+', [status(thm)], ['61', '62'])).
% 0.49/0.71  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('65', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.71  thf(d4_tops_2, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.71       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.49/0.71         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.49/0.71  thf('66', plain,
% 0.49/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.49/0.71         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.49/0.71          | ~ (v2_funct_1 @ X36)
% 0.49/0.71          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.49/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.49/0.71          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.49/0.71          | ~ (v1_funct_1 @ X36))),
% 0.49/0.71      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.71  thf('67', plain,
% 0.49/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.71        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71            = (k2_funct_1 @ sk_C))
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.71        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71            != (k2_struct_0 @ sk_B)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.71  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('69', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('70', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.71  thf('71', plain,
% 0.49/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup+', [status(thm)], ['69', '70'])).
% 0.49/0.71  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('73', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['71', '72'])).
% 0.49/0.71  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(d9_funct_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.71  thf('75', plain,
% 0.49/0.71      (![X6 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X6)
% 0.49/0.71          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.49/0.71          | ~ (v1_funct_1 @ X6)
% 0.49/0.71          | ~ (v1_relat_1 @ X6))),
% 0.49/0.71      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.71  thf('76', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.49/0.71  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('79', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('81', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('82', plain,
% 0.49/0.71      (![X32 : $i]:
% 0.49/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.71  thf('83', plain,
% 0.49/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('84', plain,
% 0.49/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71          = (k2_struct_0 @ sk_B))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.71      inference('sup+', [status(thm)], ['82', '83'])).
% 0.49/0.71  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('86', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['84', '85'])).
% 0.49/0.71  thf('87', plain,
% 0.49/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71          = (k2_struct_0 @ sk_B))
% 0.49/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.71      inference('sup+', [status(thm)], ['81', '86'])).
% 0.49/0.71  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('89', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.71  thf('90', plain,
% 0.49/0.71      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71          = (k4_relat_1 @ sk_C))
% 0.49/0.71        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.49/0.71      inference('demod', [status(thm)], ['67', '68', '73', '79', '80', '89'])).
% 0.49/0.71  thf('91', plain,
% 0.49/0.71      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('simplify', [status(thm)], ['90'])).
% 0.49/0.71  thf('92', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.71  thf(t31_funct_2, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.71       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.49/0.71         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.49/0.71           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.49/0.71           ( m1_subset_1 @
% 0.49/0.71             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.49/0.71  thf('93', plain,
% 0.49/0.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X29)
% 0.49/0.71          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.49/0.71          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 0.49/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.49/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.49/0.71          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.49/0.71          | ~ (v1_funct_1 @ X29))),
% 0.49/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.71  thf('94', plain,
% 0.49/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.71           (k1_zfmisc_1 @ 
% 0.49/0.71            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.49/0.71        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71            != (k2_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup-', [status(thm)], ['92', '93'])).
% 0.49/0.71  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('96', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['71', '72'])).
% 0.49/0.71  thf('97', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('98', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.71  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('100', plain,
% 0.49/0.71      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.71         (k1_zfmisc_1 @ 
% 0.49/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.49/0.71        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.49/0.71      inference('demod', [status(thm)], ['94', '95', '96', '97', '98', '99'])).
% 0.49/0.71  thf('101', plain,
% 0.49/0.71      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.71      inference('simplify', [status(thm)], ['100'])).
% 0.49/0.71  thf('102', plain,
% 0.49/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.49/0.71         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.49/0.71          | ~ (v2_funct_1 @ X36)
% 0.49/0.71          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.49/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.49/0.71          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.49/0.71          | ~ (v1_funct_1 @ X36))),
% 0.49/0.71      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.71  thf('103', plain,
% 0.49/0.71      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.71             (k2_struct_0 @ sk_A))
% 0.49/0.71        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.49/0.71        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71            (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['101', '102'])).
% 0.49/0.71  thf('104', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf(fc6_funct_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.49/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.49/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.49/0.71         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.49/0.71  thf('105', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('106', plain,
% 0.49/0.71      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup+', [status(thm)], ['104', '105'])).
% 0.49/0.71  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('110', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.49/0.71  thf('111', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.71  thf('112', plain,
% 0.49/0.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X29)
% 0.49/0.71          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.49/0.71          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 0.49/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.49/0.71          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.49/0.71          | ~ (v1_funct_1 @ X29))),
% 0.49/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.71  thf('113', plain,
% 0.49/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.71           (k2_struct_0 @ sk_A))
% 0.49/0.71        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71            != (k2_struct_0 @ sk_B))
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.71  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('115', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['71', '72'])).
% 0.49/0.71  thf('116', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('117', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.71         = (k2_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.71  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('119', plain,
% 0.49/0.71      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.71         (k2_struct_0 @ sk_A))
% 0.49/0.71        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.49/0.71      inference('demod', [status(thm)],
% 0.49/0.71                ['113', '114', '115', '116', '117', '118'])).
% 0.49/0.71  thf('120', plain,
% 0.49/0.71      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.71        (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('simplify', [status(thm)], ['119'])).
% 0.49/0.71  thf('121', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf(t65_funct_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.49/0.71  thf('122', plain,
% 0.49/0.71      (![X10 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X10)
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.71          | ~ (v1_funct_1 @ X10)
% 0.49/0.71          | ~ (v1_relat_1 @ X10))),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.71  thf('123', plain,
% 0.49/0.71      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.49/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup+', [status(thm)], ['121', '122'])).
% 0.49/0.71  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('127', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.49/0.71  thf('128', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('129', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v2_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('130', plain,
% 0.49/0.71      (((v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.71      inference('sup+', [status(thm)], ['128', '129'])).
% 0.49/0.71  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('134', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.49/0.71  thf('135', plain,
% 0.49/0.71      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.71      inference('simplify', [status(thm)], ['100'])).
% 0.49/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.71  thf('136', plain,
% 0.49/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.71         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.49/0.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.49/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.71  thf('137', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['135', '136'])).
% 0.49/0.71  thf(dt_k4_relat_1, axiom,
% 0.49/0.71    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.49/0.71  thf('138', plain,
% 0.49/0.71      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.49/0.71      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.71  thf('139', plain,
% 0.49/0.71      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.49/0.71      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.71  thf('140', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.49/0.71  thf('141', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('142', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v2_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('143', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v2_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('144', plain,
% 0.49/0.71      (![X10 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X10)
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.71          | ~ (v1_funct_1 @ X10)
% 0.49/0.71          | ~ (v1_relat_1 @ X10))),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.71  thf('145', plain,
% 0.49/0.71      (![X7 : $i]:
% 0.49/0.71         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.49/0.71          | ~ (v2_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_funct_1 @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X7))),
% 0.49/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.49/0.71  thf('146', plain,
% 0.49/0.71      (![X6 : $i]:
% 0.49/0.71         (~ (v2_funct_1 @ X6)
% 0.49/0.71          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.49/0.71          | ~ (v1_funct_1 @ X6)
% 0.49/0.71          | ~ (v1_relat_1 @ X6))),
% 0.49/0.71      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.71  thf('147', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['145', '146'])).
% 0.49/0.71  thf('148', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['144', '147'])).
% 0.49/0.71  thf('149', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['148'])).
% 0.49/0.71  thf('150', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['143', '149'])).
% 0.49/0.71  thf('151', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['150'])).
% 0.49/0.71  thf('152', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['142', '151'])).
% 0.49/0.71  thf('153', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['152'])).
% 0.49/0.71  thf('154', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['141', '153'])).
% 0.49/0.71  thf('155', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.71            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.71          | ~ (v2_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['154'])).
% 0.49/0.71  thf('156', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C))))
% 0.49/0.71            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C))))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['140', '155'])).
% 0.49/0.71  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('158', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.49/0.71  thf('159', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.49/0.71  thf('160', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.49/0.71  thf('161', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('162', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.49/0.71  thf('163', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.49/0.71  thf('164', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.49/0.71  thf('165', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.71        | ((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.49/0.71      inference('demod', [status(thm)],
% 0.49/0.71                ['156', '157', '158', '159', '160', '161', '162', '163', '164'])).
% 0.49/0.71  thf('166', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['139', '165'])).
% 0.49/0.71  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('168', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.71      inference('demod', [status(thm)], ['166', '167'])).
% 0.49/0.71  thf(t37_relat_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( v1_relat_1 @ A ) =>
% 0.49/0.71       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.49/0.71         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.49/0.71  thf('169', plain,
% 0.49/0.71      (![X5 : $i]:
% 0.49/0.71         (((k2_relat_1 @ X5) = (k1_relat_1 @ (k4_relat_1 @ X5)))
% 0.49/0.71          | ~ (v1_relat_1 @ X5))),
% 0.49/0.71      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.49/0.71  thf('170', plain,
% 0.49/0.71      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.49/0.71        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.71      inference('sup+', [status(thm)], ['168', '169'])).
% 0.49/0.71  thf('171', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.71        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['138', '170'])).
% 0.49/0.71  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('173', plain,
% 0.49/0.71      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['171', '172'])).
% 0.49/0.71  thf('174', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['48', '49'])).
% 0.49/0.71  thf('175', plain,
% 0.49/0.71      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('demod', [status(thm)], ['173', '174'])).
% 0.49/0.71  thf('176', plain,
% 0.49/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71         (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.71      inference('demod', [status(thm)], ['137', '175'])).
% 0.49/0.71  thf('177', plain,
% 0.49/0.71      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.49/0.71        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)],
% 0.49/0.71                ['103', '110', '120', '127', '134', '176'])).
% 0.49/0.71  thf('178', plain,
% 0.49/0.71      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.71         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.71      inference('simplify', [status(thm)], ['177'])).
% 0.49/0.71  thf('179', plain,
% 0.49/0.71      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.71          sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['60', '91', '178'])).
% 0.49/0.71  thf('180', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf('181', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_C @ 
% 0.49/0.71        (k1_zfmisc_1 @ 
% 0.49/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(reflexivity_r2_funct_2, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.71         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.71       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.49/0.71  thf('182', plain,
% 0.49/0.71      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.71         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.49/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.71          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.49/0.71          | ~ (v1_funct_1 @ X27)
% 0.49/0.71          | ~ (v1_funct_1 @ X28)
% 0.49/0.71          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.49/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.49/0.71      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.49/0.71  thf('183', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X0 @ 
% 0.49/0.71             (k1_zfmisc_1 @ 
% 0.49/0.71              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.71          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.71             sk_C))),
% 0.49/0.71      inference('sup-', [status(thm)], ['181', '182'])).
% 0.49/0.71  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('185', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('186', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X0 @ 
% 0.49/0.71             (k1_zfmisc_1 @ 
% 0.49/0.71              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.71          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.71             sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.49/0.71  thf('187', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('188', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('189', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.71      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.71  thf('190', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X0 @ 
% 0.49/0.71             (k1_zfmisc_1 @ 
% 0.49/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.71          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.71             sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.49/0.71  thf('191', plain,
% 0.49/0.71      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.49/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.71        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['180', '190'])).
% 0.49/0.71  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('193', plain,
% 0.49/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.71      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.71  thf('194', plain,
% 0.49/0.71      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.49/0.71  thf('195', plain, ($false), inference('demod', [status(thm)], ['179', '194'])).
% 0.49/0.71  
% 0.49/0.71  % SZS output end Refutation
% 0.49/0.71  
% 0.49/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
