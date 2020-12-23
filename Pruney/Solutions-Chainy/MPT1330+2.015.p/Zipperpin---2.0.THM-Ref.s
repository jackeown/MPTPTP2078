%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b07gBCgmCu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 555 expanded)
%              Number of leaves         :   29 ( 164 expanded)
%              Depth                    :   23
%              Number of atoms          : 1237 (10080 expanded)
%              Number of equality atoms :  124 ( 863 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v4_relat_1 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('18',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
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

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('32',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('35',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v4_relat_1 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('58',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('64',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k8_relset_1 @ X9 @ X10 @ X11 @ X10 )
        = ( k1_relset_1 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('68',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['48','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ k1_xboole_0 @ X14 )
      | ( v1_partfun1 @ X15 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['48','73'])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','82'])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('85',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('87',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('88',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','72'])).

thf('90',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('92',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k8_relset_1 @ X9 @ X10 @ X11 @ X10 )
        = ( k1_relset_1 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('109',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('111',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','113'])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b07gBCgmCu
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:09:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 140 iterations in 0.048s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.47  thf(d3_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf(t52_tops_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_struct_0 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( l1_struct_0 @ B ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.47                 ( m1_subset_1 @
% 0.19/0.47                   C @ 
% 0.19/0.47                   ( k1_zfmisc_1 @
% 0.19/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.47               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.47                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.47                 ( ( k8_relset_1 @
% 0.19/0.47                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.47                     ( k2_struct_0 @ B ) ) =
% 0.19/0.47                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( l1_struct_0 @ A ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( l1_struct_0 @ B ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47                    ( v1_funct_2 @
% 0.19/0.47                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.47                    ( m1_subset_1 @
% 0.19/0.47                      C @ 
% 0.19/0.47                      ( k1_zfmisc_1 @
% 0.19/0.47                        ( k2_zfmisc_1 @
% 0.19/0.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.47                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.47                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.47                    ( ( k8_relset_1 @
% 0.19/0.47                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.47                        ( k2_struct_0 @ B ) ) =
% 0.19/0.47                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t132_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.47           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.47         (((X14) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_funct_1 @ X15)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | (v1_partfun1 @ X15 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.19/0.47          | ~ (v1_funct_1 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.47         (~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.19/0.47          | (v1_partfun1 @ X15 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | ~ (v1_funct_1 @ X15)
% 0.19/0.47          | ((X14) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.47  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.47  thf(d4_partfun1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.47       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (v1_partfun1 @ X13 @ X12)
% 0.19/0.47          | ((k1_relat_1 @ X13) = (X12))
% 0.19/0.47          | ~ (v4_relat_1 @ X13 @ X12)
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc1_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( v1_relat_1 @ C ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((v1_relat_1 @ X0)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.47  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         ((v4_relat_1 @ X3 @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.47  thf('16', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_B)
% 0.19/0.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '17'])).
% 0.19/0.47  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.19/0.47        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.19/0.47         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ 
% 0.19/0.47          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['23', '28'])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['23', '28'])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.47         (~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.19/0.47          | (v1_partfun1 @ X15 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | ~ (v1_funct_1 @ X15)
% 0.19/0.47          | ((X14) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('32', plain,
% 0.19/0.47      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47         | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.19/0.47         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.47  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.47  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('39', plain,
% 0.19/0.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.47  thf('40', plain,
% 0.19/0.47      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['34', '39'])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['32', '33', '40'])).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (v1_partfun1 @ X13 @ X12)
% 0.19/0.47          | ((k1_relat_1 @ X13) = (X12))
% 0.19/0.47          | ~ (v4_relat_1 @ X13 @ X12)
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47         | ~ (v1_relat_1 @ sk_C)
% 0.19/0.47         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.19/0.47         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.47  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['23', '28'])).
% 0.19/0.47  thf('46', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         ((v4_relat_1 @ X3 @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.47  thf('47', plain,
% 0.19/0.47      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.47  thf('48', plain,
% 0.19/0.47      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.47         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.19/0.47  thf('49', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('50', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('51', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('53', plain,
% 0.19/0.47      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.47  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('55', plain,
% 0.19/0.47      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.47  thf('56', plain,
% 0.19/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['50', '55'])).
% 0.19/0.47  thf('57', plain,
% 0.19/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('58', plain,
% 0.19/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['56', '57'])).
% 0.19/0.47  thf('59', plain,
% 0.19/0.47      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.19/0.47         | ~ (l1_struct_0 @ sk_B)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['49', '58'])).
% 0.19/0.47  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('61', plain,
% 0.19/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.47  thf('62', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('63', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['23', '28'])).
% 0.19/0.47  thf('64', plain,
% 0.19/0.47      ((((m1_subset_1 @ sk_C @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.19/0.47         | ~ (l1_struct_0 @ sk_B)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['62', '63'])).
% 0.19/0.47  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('66', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.47  thf(t38_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.47         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.47  thf('67', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         (((k8_relset_1 @ X9 @ X10 @ X11 @ X10)
% 0.19/0.47            = (k1_relset_1 @ X9 @ X10 @ X11))
% 0.19/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.19/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.47  thf('68', plain,
% 0.19/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B))
% 0.19/0.47          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['66', '67'])).
% 0.19/0.47  thf('69', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('70', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.47         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.19/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.47  thf('71', plain,
% 0.19/0.47      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.47          = (k1_relat_1 @ sk_C)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['69', '70'])).
% 0.19/0.47  thf('72', plain,
% 0.19/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['68', '71'])).
% 0.19/0.47  thf('73', plain,
% 0.19/0.47      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['61', '72'])).
% 0.19/0.47  thf('74', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['48', '73'])).
% 0.19/0.47  thf('75', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['29', '74'])).
% 0.19/0.47  thf('76', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.47         (((X16) != (k1_xboole_0))
% 0.19/0.47          | ~ (v1_funct_1 @ X15)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | (v1_partfun1 @ X15 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.19/0.47          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.19/0.47          | ~ (v1_funct_1 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.47  thf('77', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i]:
% 0.19/0.47         (~ (v1_funct_2 @ X15 @ k1_xboole_0 @ X14)
% 0.19/0.47          | (v1_partfun1 @ X15 @ k1_xboole_0)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ 
% 0.19/0.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X14)))
% 0.19/0.47          | ~ (v1_funct_1 @ X15))),
% 0.19/0.47      inference('simplify', [status(thm)], ['76'])).
% 0.19/0.47  thf('78', plain,
% 0.19/0.47      (((~ (v1_funct_1 @ sk_C)
% 0.19/0.47         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.19/0.47         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['75', '77'])).
% 0.19/0.47  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('80', plain,
% 0.19/0.47      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['34', '39'])).
% 0.19/0.47  thf('81', plain,
% 0.19/0.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['48', '73'])).
% 0.19/0.47  thf('82', plain,
% 0.19/0.47      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.47  thf('83', plain,
% 0.19/0.47      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['78', '79', '82'])).
% 0.19/0.47  thf('84', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (v1_partfun1 @ X13 @ X12)
% 0.19/0.47          | ((k1_relat_1 @ X13) = (X12))
% 0.19/0.47          | ~ (v4_relat_1 @ X13 @ X12)
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.47  thf('85', plain,
% 0.19/0.47      (((~ (v1_relat_1 @ sk_C)
% 0.19/0.47         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.19/0.47         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['83', '84'])).
% 0.19/0.47  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('87', plain,
% 0.19/0.47      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.47  thf('88', plain,
% 0.19/0.47      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.19/0.47  thf('89', plain,
% 0.19/0.47      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.19/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['61', '72'])).
% 0.19/0.47  thf('90', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.19/0.47  thf('91', plain,
% 0.19/0.47      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.19/0.47       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('split', [status(esa)], ['21'])).
% 0.19/0.47  thf('92', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.19/0.47  thf('93', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['22', '92'])).
% 0.19/0.47  thf('94', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['20', '93'])).
% 0.19/0.47  thf('95', plain,
% 0.19/0.47      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['0', '94'])).
% 0.19/0.47  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('97', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['95', '96'])).
% 0.19/0.47  thf('98', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('99', plain,
% 0.19/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('100', plain,
% 0.19/0.47      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['98', '99'])).
% 0.19/0.47  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('102', plain,
% 0.19/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['100', '101'])).
% 0.19/0.47  thf('103', plain,
% 0.19/0.47      (![X17 : $i]:
% 0.19/0.47         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.47  thf('104', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('105', plain,
% 0.19/0.47      (((m1_subset_1 @ sk_C @ 
% 0.19/0.47         (k1_zfmisc_1 @ 
% 0.19/0.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.19/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.47      inference('sup+', [status(thm)], ['103', '104'])).
% 0.19/0.47  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('107', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.47      inference('demod', [status(thm)], ['105', '106'])).
% 0.19/0.47  thf('108', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         (((k8_relset_1 @ X9 @ X10 @ X11 @ X10)
% 0.19/0.47            = (k1_relset_1 @ X9 @ X10 @ X11))
% 0.19/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.19/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.47  thf('109', plain,
% 0.19/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B))
% 0.19/0.47         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.47  thf('110', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.47      inference('demod', [status(thm)], ['105', '106'])).
% 0.19/0.47  thf('111', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.47         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.19/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.47  thf('112', plain,
% 0.19/0.47      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.47         = (k1_relat_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['110', '111'])).
% 0.19/0.47  thf('113', plain,
% 0.19/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.47         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.19/0.47      inference('demod', [status(thm)], ['109', '112'])).
% 0.19/0.47  thf('114', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['102', '113'])).
% 0.19/0.47  thf('115', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['97', '114'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
