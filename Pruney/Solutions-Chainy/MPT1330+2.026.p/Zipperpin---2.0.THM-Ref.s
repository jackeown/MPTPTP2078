%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wn5WLlCb4q

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 567 expanded)
%              Number of leaves         :   30 ( 168 expanded)
%              Depth                    :   23
%              Number of atoms          : 1253 (10144 expanded)
%              Number of equality atoms :  124 ( 863 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('34',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('37',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('53',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('60',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('66',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k8_relset_1 @ X10 @ X11 @ X12 @ X11 )
        = ( k1_relset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('70',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','74'])).

thf('76',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','76'])).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ k1_xboole_0 @ X15 )
      | ( v1_partfun1 @ X16 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','75'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('87',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('89',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('90',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','74'])).

thf('92',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('94',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','95'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k8_relset_1 @ X10 @ X11 @ X12 @ X11 )
        = ( k1_relset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('111',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('113',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('114',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','115'])).

thf('117',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wn5WLlCb4q
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 137 iterations in 0.059s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(d3_struct_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf(t52_tops_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_struct_0 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( l1_struct_0 @ B ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.54                 ( m1_subset_1 @
% 0.35/0.54                   C @ 
% 0.35/0.54                   ( k1_zfmisc_1 @
% 0.35/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.54               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54                 ( ( k8_relset_1 @
% 0.35/0.54                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.35/0.54                     ( k2_struct_0 @ B ) ) =
% 0.35/0.54                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( l1_struct_0 @ A ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( l1_struct_0 @ B ) =>
% 0.35/0.54              ( ![C:$i]:
% 0.35/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.54                    ( v1_funct_2 @
% 0.35/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.54                    ( m1_subset_1 @
% 0.35/0.54                      C @ 
% 0.35/0.54                      ( k1_zfmisc_1 @
% 0.35/0.54                        ( k2_zfmisc_1 @
% 0.35/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.54                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54                    ( ( k8_relset_1 @
% 0.35/0.54                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.35/0.54                        ( k2_struct_0 @ B ) ) =
% 0.35/0.54                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t132_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.54           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (((X15) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_funct_1 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.35/0.54          | ~ (v1_funct_1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.35/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | ~ (v1_funct_1 @ X16)
% 0.35/0.54          | ((X15) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.35/0.54  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.54  thf(d4_partfun1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (v1_partfun1 @ X14 @ X13)
% 0.35/0.54          | ((k1_relat_1 @ X14) = (X13))
% 0.35/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.54        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.54          | (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ 
% 0.35/0.54           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.35/0.54        | (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf(fc6_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.54  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         ((v4_relat_1 @ X4 @ X5)
% 0.35/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('18', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.35/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['1', '19'])).
% 0.35/0.54  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.35/0.54        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.35/0.54         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ 
% 0.35/0.54          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.35/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | ~ (v1_funct_1 @ X16)
% 0.35/0.54          | ((X15) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54         | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.35/0.54         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['36', '41'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '35', '42'])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (v1_partfun1 @ X14 @ X13)
% 0.35/0.54          | ((k1_relat_1 @ X14) = (X13))
% 0.35/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54         | ~ (v1_relat_1 @ sk_C)
% 0.35/0.54         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.35/0.54         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         ((v4_relat_1 @ X4 @ X5)
% 0.35/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.54         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.35/0.54  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['52', '57'])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_B)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['51', '60'])).
% 0.35/0.54  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '62'])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      ((((m1_subset_1 @ sk_C @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_B)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['64', '65'])).
% 0.35/0.54  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.35/0.54  thf(t38_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.35/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (((k8_relset_1 @ X10 @ X11 @ X12 @ X11)
% 0.35/0.54            = (k1_relset_1 @ X10 @ X11 @ X12))
% 0.35/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.54      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B))
% 0.35/0.54          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.35/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('73', plain,
% 0.35/0.54      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.35/0.54          = (k1_relat_1 @ sk_C)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.35/0.54  thf('74', plain,
% 0.35/0.54      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['70', '73'])).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['63', '74'])).
% 0.35/0.54  thf('76', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['50', '75'])).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['31', '76'])).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (((X17) != (k1_xboole_0))
% 0.35/0.54          | ~ (v1_funct_1 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.35/0.54          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.35/0.54          | ~ (v1_funct_1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X16 @ k1_xboole_0 @ X15)
% 0.35/0.54          | (v1_partfun1 @ X16 @ k1_xboole_0)
% 0.35/0.54          | ~ (m1_subset_1 @ X16 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X15)))
% 0.35/0.54          | ~ (v1_funct_1 @ X16))),
% 0.35/0.54      inference('simplify', [status(thm)], ['78'])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      (((~ (v1_funct_1 @ sk_C)
% 0.35/0.54         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.35/0.54         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['77', '79'])).
% 0.35/0.54  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['36', '41'])).
% 0.35/0.54  thf('83', plain,
% 0.35/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['50', '75'])).
% 0.35/0.54  thf('84', plain,
% 0.35/0.54      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['82', '83'])).
% 0.35/0.54  thf('85', plain,
% 0.35/0.54      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.35/0.54  thf('86', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (v1_partfun1 @ X14 @ X13)
% 0.35/0.54          | ((k1_relat_1 @ X14) = (X13))
% 0.35/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.54  thf('87', plain,
% 0.35/0.54      (((~ (v1_relat_1 @ sk_C)
% 0.35/0.54         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.35/0.54         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.35/0.54  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('89', plain,
% 0.35/0.54      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.54  thf('90', plain,
% 0.35/0.54      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.35/0.54  thf('91', plain,
% 0.35/0.54      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.35/0.54         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['63', '74'])).
% 0.35/0.54  thf('92', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.35/0.54  thf('93', plain,
% 0.35/0.54      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.35/0.54       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('split', [status(esa)], ['23'])).
% 0.35/0.54  thf('94', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.35/0.54  thf('95', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['24', '94'])).
% 0.35/0.54  thf('96', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['22', '95'])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['0', '96'])).
% 0.35/0.54  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('99', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.35/0.54  thf('100', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('101', plain,
% 0.35/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('102', plain,
% 0.35/0.54      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['100', '101'])).
% 0.35/0.54  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('104', plain,
% 0.35/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.54         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['102', '103'])).
% 0.35/0.54  thf('105', plain,
% 0.35/0.54      (![X18 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('106', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('107', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_C @ 
% 0.35/0.54         (k1_zfmisc_1 @ 
% 0.35/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.54      inference('sup+', [status(thm)], ['105', '106'])).
% 0.35/0.54  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('109', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.35/0.55      inference('demod', [status(thm)], ['107', '108'])).
% 0.35/0.55  thf('110', plain,
% 0.35/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.55         (((k8_relset_1 @ X10 @ X11 @ X12 @ X11)
% 0.35/0.55            = (k1_relset_1 @ X10 @ X11 @ X12))
% 0.35/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.55      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.35/0.55  thf('111', plain,
% 0.35/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.55         (k2_struct_0 @ sk_B))
% 0.35/0.55         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['109', '110'])).
% 0.35/0.55  thf('112', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.35/0.55      inference('demod', [status(thm)], ['107', '108'])).
% 0.35/0.55  thf('113', plain,
% 0.35/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.55         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.35/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.55  thf('114', plain,
% 0.35/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.35/0.55         = (k1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['112', '113'])).
% 0.35/0.55  thf('115', plain,
% 0.35/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.55         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['111', '114'])).
% 0.35/0.55  thf('116', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['104', '115'])).
% 0.35/0.55  thf('117', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['99', '116'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
