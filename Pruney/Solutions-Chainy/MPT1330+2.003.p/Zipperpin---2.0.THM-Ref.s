%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7EoYS8D73Y

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:41 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 297 expanded)
%              Number of leaves         :   48 ( 106 expanded)
%              Depth                    :   23
%              Number of atoms          : 1347 (3674 expanded)
%              Number of equality atoms :  146 ( 339 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('13',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ( v1_partfun1 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ( v1_partfun1 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('31',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_partfun1 @ X42 @ X41 )
      | ( ( k1_relat_1 @ X42 )
        = X41 )
      | ~ ( v4_relat_1 @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('32',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('48',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('57',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('58',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('74',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('78',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('85',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('92',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('104',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('105',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_C )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('107',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ sk_C )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(fc17_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc17_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('109',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('110',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k1_xboole_0 = sk_C )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','118'])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ X0 @ ( k2_struct_0 @ sk_B_1 ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','122'])).

thf('124',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('129',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['47','129'])).

thf('131',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','130'])).

thf('132',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7EoYS8D73Y
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.53/2.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.53/2.73  % Solved by: fo/fo7.sh
% 2.53/2.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.73  % done 3712 iterations in 2.270s
% 2.53/2.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.53/2.73  % SZS output start Refutation
% 2.53/2.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.53/2.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.53/2.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.53/2.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.53/2.73  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.53/2.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.53/2.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.53/2.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.53/2.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.53/2.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.53/2.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.53/2.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.53/2.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.53/2.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.53/2.73  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.53/2.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.53/2.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.53/2.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.53/2.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.53/2.73  thf(sk_C_type, type, sk_C: $i).
% 2.53/2.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.53/2.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.53/2.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.53/2.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.53/2.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.73  thf(d3_struct_0, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.53/2.73  thf('0', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf(t52_tops_2, conjecture,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( l1_struct_0 @ A ) =>
% 2.53/2.73       ( ![B:$i]:
% 2.53/2.73         ( ( l1_struct_0 @ B ) =>
% 2.53/2.73           ( ![C:$i]:
% 2.53/2.73             ( ( ( v1_funct_1 @ C ) & 
% 2.53/2.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.53/2.73                 ( m1_subset_1 @
% 2.53/2.73                   C @ 
% 2.53/2.73                   ( k1_zfmisc_1 @
% 2.53/2.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.53/2.73               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 2.53/2.73                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.53/2.73                 ( ( k8_relset_1 @
% 2.53/2.73                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.53/2.73                     ( k2_struct_0 @ B ) ) =
% 2.53/2.73                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 2.53/2.73  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.73    (~( ![A:$i]:
% 2.53/2.73        ( ( l1_struct_0 @ A ) =>
% 2.53/2.73          ( ![B:$i]:
% 2.53/2.73            ( ( l1_struct_0 @ B ) =>
% 2.53/2.73              ( ![C:$i]:
% 2.53/2.73                ( ( ( v1_funct_1 @ C ) & 
% 2.53/2.73                    ( v1_funct_2 @
% 2.53/2.73                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.53/2.73                    ( m1_subset_1 @
% 2.53/2.73                      C @ 
% 2.53/2.73                      ( k1_zfmisc_1 @
% 2.53/2.73                        ( k2_zfmisc_1 @
% 2.53/2.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.53/2.73                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 2.53/2.73                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.53/2.73                    ( ( k8_relset_1 @
% 2.53/2.73                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.53/2.73                        ( k2_struct_0 @ B ) ) =
% 2.53/2.73                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 2.53/2.73    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 2.53/2.73  thf('1', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf(cc2_relset_1, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i]:
% 2.53/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.53/2.73  thf('2', plain,
% 2.53/2.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.53/2.73         ((v5_relat_1 @ X28 @ X30)
% 2.53/2.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.53/2.73  thf('3', plain, ((v5_relat_1 @ sk_C @ (u1_struct_0 @ sk_B_1))),
% 2.53/2.73      inference('sup-', [status(thm)], ['1', '2'])).
% 2.53/2.73  thf(d19_relat_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ B ) =>
% 2.53/2.73       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.53/2.73  thf('4', plain,
% 2.53/2.73      (![X6 : $i, X7 : $i]:
% 2.53/2.73         (~ (v5_relat_1 @ X6 @ X7)
% 2.53/2.73          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 2.53/2.73          | ~ (v1_relat_1 @ X6))),
% 2.53/2.73      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.53/2.73  thf('5', plain,
% 2.53/2.73      ((~ (v1_relat_1 @ sk_C)
% 2.53/2.73        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['3', '4'])).
% 2.53/2.73  thf('6', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf(cc1_relset_1, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i]:
% 2.53/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.73       ( v1_relat_1 @ C ) ))).
% 2.53/2.73  thf('7', plain,
% 2.53/2.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.53/2.73         ((v1_relat_1 @ X25)
% 2.53/2.73          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.53/2.73  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.53/2.73      inference('demod', [status(thm)], ['5', '8'])).
% 2.53/2.73  thf(t79_relat_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ B ) =>
% 2.53/2.73       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.53/2.73         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.53/2.73  thf('10', plain,
% 2.53/2.73      (![X19 : $i, X20 : $i]:
% 2.53/2.73         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 2.53/2.73          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 2.53/2.73          | ~ (v1_relat_1 @ X19))),
% 2.53/2.73      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.53/2.73  thf('11', plain,
% 2.53/2.73      ((~ (v1_relat_1 @ sk_C)
% 2.53/2.73        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B_1))) = (sk_C)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['9', '10'])).
% 2.53/2.73  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf('13', plain,
% 2.53/2.73      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B_1))) = (sk_C))),
% 2.53/2.73      inference('demod', [status(thm)], ['11', '12'])).
% 2.53/2.73  thf(t71_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.53/2.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.53/2.73  thf('14', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 2.53/2.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.53/2.73  thf(t182_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ A ) =>
% 2.53/2.73       ( ![B:$i]:
% 2.53/2.73         ( ( v1_relat_1 @ B ) =>
% 2.53/2.73           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.53/2.73             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.53/2.73  thf('15', plain,
% 2.53/2.73      (![X13 : $i, X14 : $i]:
% 2.53/2.73         (~ (v1_relat_1 @ X13)
% 2.53/2.73          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 2.53/2.73              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 2.53/2.73          | ~ (v1_relat_1 @ X14))),
% 2.53/2.73      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.53/2.73  thf('16', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.53/2.73            = (k10_relat_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_relat_1 @ X1)
% 2.53/2.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['14', '15'])).
% 2.53/2.73  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.53/2.73  thf('17', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 2.53/2.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.53/2.73  thf('18', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.53/2.73            = (k10_relat_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_relat_1 @ X1))),
% 2.53/2.73      inference('demod', [status(thm)], ['16', '17'])).
% 2.53/2.73  thf('19', plain,
% 2.53/2.73      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B_1)))
% 2.53/2.73        | ~ (v1_relat_1 @ sk_C))),
% 2.53/2.73      inference('sup+', [status(thm)], ['13', '18'])).
% 2.53/2.73  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf('21', plain,
% 2.53/2.73      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B_1)))),
% 2.53/2.73      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.73  thf('22', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf('23', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf('24', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf(t132_funct_2, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i]:
% 2.53/2.73     ( ( ( v1_funct_1 @ C ) & 
% 2.53/2.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.53/2.73       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.53/2.73           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.53/2.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.53/2.73           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.53/2.73  thf('25', plain,
% 2.53/2.73      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.53/2.73         (((X43) = (k1_xboole_0))
% 2.53/2.73          | ~ (v1_funct_1 @ X44)
% 2.53/2.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 2.53/2.73          | (v1_partfun1 @ X44 @ X45)
% 2.53/2.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 2.53/2.73          | ~ (v1_funct_2 @ X44 @ X45 @ X43)
% 2.53/2.73          | ~ (v1_funct_1 @ X44))),
% 2.53/2.73      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.53/2.73  thf('26', plain,
% 2.53/2.73      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.53/2.73         (~ (v1_funct_2 @ X44 @ X45 @ X43)
% 2.53/2.73          | (v1_partfun1 @ X44 @ X45)
% 2.53/2.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 2.53/2.73          | ~ (v1_funct_1 @ X44)
% 2.53/2.73          | ((X43) = (k1_xboole_0)))),
% 2.53/2.73      inference('simplify', [status(thm)], ['25'])).
% 2.53/2.73  thf('27', plain,
% 2.53/2.73      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | ~ (v1_funct_1 @ sk_C)
% 2.53/2.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.53/2.73        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['24', '26'])).
% 2.53/2.73  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('29', plain,
% 2.53/2.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('30', plain,
% 2.53/2.73      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.53/2.73  thf(d4_partfun1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.53/2.73       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.53/2.73  thf('31', plain,
% 2.53/2.73      (![X41 : $i, X42 : $i]:
% 2.53/2.73         (~ (v1_partfun1 @ X42 @ X41)
% 2.53/2.73          | ((k1_relat_1 @ X42) = (X41))
% 2.53/2.73          | ~ (v4_relat_1 @ X42 @ X41)
% 2.53/2.73          | ~ (v1_relat_1 @ X42))),
% 2.53/2.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.53/2.73  thf('32', plain,
% 2.53/2.73      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | ~ (v1_relat_1 @ sk_C)
% 2.53/2.73        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.53/2.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['30', '31'])).
% 2.53/2.73  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf('34', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('35', plain,
% 2.53/2.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.53/2.73         ((v4_relat_1 @ X28 @ X29)
% 2.53/2.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.53/2.73  thf('36', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.53/2.73      inference('sup-', [status(thm)], ['34', '35'])).
% 2.53/2.73  thf('37', plain,
% 2.53/2.73      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('demod', [status(thm)], ['32', '33', '36'])).
% 2.53/2.73  thf('38', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_B_1)
% 2.53/2.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['23', '37'])).
% 2.53/2.73  thf('39', plain, ((l1_struct_0 @ sk_B_1)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('40', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.53/2.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('demod', [status(thm)], ['38', '39'])).
% 2.53/2.73  thf('41', plain,
% 2.53/2.73      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_A)
% 2.53/2.73        | ((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['22', '40'])).
% 2.53/2.73  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('43', plain,
% 2.53/2.73      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 2.53/2.73        | ((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.53/2.73      inference('demod', [status(thm)], ['41', '42'])).
% 2.53/2.73  thf('44', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.53/2.73        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('45', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 2.53/2.73         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('46', plain,
% 2.53/2.73      (((((k1_xboole_0) != (k1_xboole_0))
% 2.53/2.73         | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))))
% 2.53/2.73         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['43', '45'])).
% 2.53/2.73  thf('47', plain,
% 2.53/2.73      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 2.53/2.73         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.53/2.73      inference('simplify', [status(thm)], ['46'])).
% 2.53/2.73  thf(t60_relat_1, axiom,
% 2.53/2.73    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.53/2.73     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.53/2.73  thf('48', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.53/2.73  thf('49', plain,
% 2.53/2.73      (![X19 : $i, X20 : $i]:
% 2.53/2.73         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 2.53/2.73          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 2.53/2.73          | ~ (v1_relat_1 @ X19))),
% 2.53/2.73      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.53/2.73  thf('50', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.53/2.73          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['48', '49'])).
% 2.53/2.73  thf(t113_zfmisc_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.53/2.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.53/2.73  thf('51', plain,
% 2.53/2.73      (![X3 : $i, X4 : $i]:
% 2.53/2.73         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.53/2.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.53/2.73  thf('52', plain,
% 2.53/2.73      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.53/2.73      inference('simplify', [status(thm)], ['51'])).
% 2.53/2.73  thf(t194_relat_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 2.53/2.73  thf('53', plain,
% 2.53/2.73      (![X15 : $i, X16 : $i]:
% 2.53/2.73         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 2.53/2.73      inference('cnf', [status(esa)], [t194_relat_1])).
% 2.53/2.73  thf('54', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.53/2.73      inference('sup+', [status(thm)], ['52', '53'])).
% 2.53/2.73  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.53/2.73  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.53/2.73      inference('demod', [status(thm)], ['54', '55'])).
% 2.53/2.73  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.53/2.73  thf('57', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.53/2.73  thf('58', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 2.53/2.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.53/2.73  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.53/2.73      inference('sup+', [status(thm)], ['57', '58'])).
% 2.53/2.73  thf('60', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 2.53/2.73      inference('demod', [status(thm)], ['50', '56', '59'])).
% 2.53/2.73  thf('61', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.53/2.73            = (k10_relat_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_relat_1 @ X1))),
% 2.53/2.73      inference('demod', [status(thm)], ['16', '17'])).
% 2.53/2.73  thf('62', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (((k1_relat_1 @ k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 2.53/2.73          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['60', '61'])).
% 2.53/2.73  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.53/2.73  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.53/2.73      inference('sup+', [status(thm)], ['57', '58'])).
% 2.53/2.73  thf('65', plain,
% 2.53/2.73      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 2.53/2.73      inference('demod', [status(thm)], ['62', '63', '64'])).
% 2.53/2.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.53/2.73  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.53/2.73  thf(t8_boole, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.53/2.73  thf('67', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.53/2.73      inference('cnf', [status(esa)], [t8_boole])).
% 2.53/2.73  thf('68', plain,
% 2.53/2.73      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['66', '67'])).
% 2.53/2.73  thf('69', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf('70', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('71', plain,
% 2.53/2.73      (((m1_subset_1 @ sk_C @ 
% 2.53/2.73         (k1_zfmisc_1 @ 
% 2.53/2.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_A))),
% 2.53/2.73      inference('sup+', [status(thm)], ['69', '70'])).
% 2.53/2.73  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('73', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('demod', [status(thm)], ['71', '72'])).
% 2.53/2.73  thf(redefinition_k8_relset_1, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i,D:$i]:
% 2.53/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.73       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.53/2.73  thf('74', plain,
% 2.53/2.73      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.53/2.73         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.53/2.73          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 2.53/2.73      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.53/2.73  thf('75', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.53/2.73           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['73', '74'])).
% 2.53/2.73  thf('76', plain,
% 2.53/2.73      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['66', '67'])).
% 2.53/2.73  thf('77', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('78', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf('79', plain,
% 2.53/2.73      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('80', plain,
% 2.53/2.73      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_A))),
% 2.53/2.73      inference('sup-', [status(thm)], ['78', '79'])).
% 2.53/2.73  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('82', plain,
% 2.53/2.73      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.53/2.73      inference('demod', [status(thm)], ['80', '81'])).
% 2.53/2.73  thf('83', plain,
% 2.53/2.73      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['77', '82'])).
% 2.53/2.73  thf('84', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('85', plain,
% 2.53/2.73      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['83', '84'])).
% 2.53/2.73  thf('86', plain,
% 2.53/2.73      ((![X0 : $i]:
% 2.53/2.73          (((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73             (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.53/2.73           | ~ (v1_xboole_0 @ X0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['76', '85'])).
% 2.53/2.73  thf('87', plain,
% 2.53/2.73      (((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.53/2.73         | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['75', '86'])).
% 2.53/2.73  thf('88', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.53/2.73  thf('90', plain,
% 2.53/2.73      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['87', '88', '89'])).
% 2.53/2.73  thf('91', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('92', plain,
% 2.53/2.73      (![X46 : $i]:
% 2.53/2.73         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.53/2.73  thf('93', plain,
% 2.53/2.73      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['66', '67'])).
% 2.53/2.73  thf('94', plain,
% 2.53/2.73      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.53/2.73      inference('simplify', [status(thm)], ['51'])).
% 2.53/2.73  thf('95', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['93', '94'])).
% 2.53/2.73  thf('96', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('97', plain,
% 2.53/2.73      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.53/2.73        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['95', '96'])).
% 2.53/2.73  thf('98', plain,
% 2.53/2.73      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_A)
% 2.53/2.73        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['92', '97'])).
% 2.53/2.73  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('100', plain,
% 2.53/2.73      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.53/2.73        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.53/2.73      inference('demod', [status(thm)], ['98', '99'])).
% 2.53/2.73  thf('101', plain,
% 2.53/2.73      (((~ (v1_xboole_0 @ k1_xboole_0)
% 2.53/2.73         | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['91', '100'])).
% 2.53/2.73  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.53/2.73  thf('103', plain,
% 2.53/2.73      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['101', '102'])).
% 2.53/2.73  thf(t162_funct_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.53/2.73       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 2.53/2.73  thf('104', plain,
% 2.53/2.73      (![X21 : $i, X22 : $i]:
% 2.53/2.73         (((k9_relat_1 @ (k6_relat_1 @ X22) @ X21) = (X21))
% 2.53/2.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 2.53/2.73      inference('cnf', [status(esa)], [t162_funct_1])).
% 2.53/2.73  thf('105', plain,
% 2.53/2.73      ((((k9_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ sk_C) = (sk_C)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['103', '104'])).
% 2.53/2.73  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.53/2.73  thf('107', plain,
% 2.53/2.73      ((((k9_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['105', '106'])).
% 2.53/2.73  thf(fc17_relat_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) ) =>
% 2.53/2.73       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 2.53/2.73         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 2.53/2.73  thf('108', plain,
% 2.53/2.73      (![X9 : $i, X10 : $i]:
% 2.53/2.73         (~ (v1_relat_1 @ X9)
% 2.53/2.73          | ~ (v1_xboole_0 @ X9)
% 2.53/2.73          | (v1_xboole_0 @ (k7_relat_1 @ X9 @ X10)))),
% 2.53/2.73      inference('cnf', [status(esa)], [fc17_relat_1])).
% 2.53/2.73  thf(cc1_relat_1, axiom,
% 2.53/2.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.53/2.73  thf('109', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.53/2.73  thf('110', plain,
% 2.53/2.73      (![X9 : $i, X10 : $i]:
% 2.53/2.73         ((v1_xboole_0 @ (k7_relat_1 @ X9 @ X10)) | ~ (v1_xboole_0 @ X9))),
% 2.53/2.73      inference('clc', [status(thm)], ['108', '109'])).
% 2.53/2.73  thf('111', plain,
% 2.53/2.73      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['66', '67'])).
% 2.53/2.73  thf('112', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['110', '111'])).
% 2.53/2.73  thf(t148_relat_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ B ) =>
% 2.53/2.73       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.53/2.73  thf('113', plain,
% 2.53/2.73      (![X11 : $i, X12 : $i]:
% 2.53/2.73         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 2.53/2.73          | ~ (v1_relat_1 @ X11))),
% 2.53/2.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.53/2.73  thf('114', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X1)
% 2.53/2.73          | ~ (v1_relat_1 @ X1))),
% 2.53/2.73      inference('sup+', [status(thm)], ['112', '113'])).
% 2.53/2.73  thf('115', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.53/2.73  thf('116', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X1)
% 2.53/2.73          | ~ (v1_relat_1 @ X1))),
% 2.53/2.73      inference('demod', [status(thm)], ['114', '115'])).
% 2.53/2.73  thf('117', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.53/2.73  thf('118', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k9_relat_1 @ X1 @ X0)))),
% 2.53/2.73      inference('clc', [status(thm)], ['116', '117'])).
% 2.53/2.73  thf('119', plain,
% 2.53/2.73      (((((k1_xboole_0) = (sk_C)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup+', [status(thm)], ['107', '118'])).
% 2.53/2.73  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.53/2.73  thf('121', plain,
% 2.53/2.73      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['119', '120'])).
% 2.53/2.73  thf('122', plain,
% 2.53/2.73      ((((k10_relat_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['90', '121'])).
% 2.53/2.73  thf('123', plain,
% 2.53/2.73      ((![X0 : $i]:
% 2.53/2.73          (((k10_relat_1 @ X0 @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.53/2.73           | ~ (v1_xboole_0 @ X0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['68', '122'])).
% 2.53/2.73  thf('124', plain,
% 2.53/2.73      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('sup-', [status(thm)], ['65', '123'])).
% 2.53/2.73  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.53/2.73  thf('126', plain,
% 2.53/2.73      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.53/2.73         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.53/2.73      inference('demod', [status(thm)], ['124', '125'])).
% 2.53/2.73  thf('127', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.53/2.73      inference('simplify', [status(thm)], ['126'])).
% 2.53/2.73  thf('128', plain,
% 2.53/2.73      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 2.53/2.73       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.53/2.73      inference('split', [status(esa)], ['44'])).
% 2.53/2.73  thf('129', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.53/2.73      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 2.53/2.73  thf('130', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.53/2.73      inference('simpl_trail', [status(thm)], ['47', '129'])).
% 2.53/2.73  thf('131', plain,
% 2.53/2.73      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B_1)))),
% 2.53/2.73      inference('demod', [status(thm)], ['21', '130'])).
% 2.53/2.73  thf('132', plain,
% 2.53/2.73      ((((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))
% 2.53/2.73        | ~ (l1_struct_0 @ sk_B_1))),
% 2.53/2.73      inference('sup+', [status(thm)], ['0', '131'])).
% 2.53/2.73  thf('133', plain, ((l1_struct_0 @ sk_B_1)),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('134', plain,
% 2.53/2.73      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))),
% 2.53/2.73      inference('demod', [status(thm)], ['132', '133'])).
% 2.53/2.73  thf('135', plain,
% 2.53/2.73      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.53/2.73         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('136', plain,
% 2.53/2.73      ((m1_subset_1 @ sk_C @ 
% 2.53/2.73        (k1_zfmisc_1 @ 
% 2.53/2.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('137', plain,
% 2.53/2.73      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.53/2.73         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.53/2.73          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 2.53/2.73      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.53/2.73  thf('138', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.53/2.73           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['136', '137'])).
% 2.53/2.73  thf('139', plain,
% 2.53/2.73      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.53/2.73      inference('demod', [status(thm)], ['135', '138'])).
% 2.53/2.73  thf('140', plain, ($false),
% 2.53/2.73      inference('simplify_reflect-', [status(thm)], ['134', '139'])).
% 2.53/2.73  
% 2.53/2.73  % SZS output end Refutation
% 2.53/2.73  
% 2.53/2.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
