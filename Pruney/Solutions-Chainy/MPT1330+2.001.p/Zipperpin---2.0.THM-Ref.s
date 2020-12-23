%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UKeqijnxZ5

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 324 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          : 1133 (5575 expanded)
%              Number of equality atoms :  105 ( 461 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
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
    inference(split,[status(esa)],['22'])).

thf('35',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('45',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X15 ) ) )
      | ( v1_partfun1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('49',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('52',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','56'])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('60',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('67',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('73',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k8_relset_1 @ X10 @ X11 @ X12 @ X11 )
        = ( k1_relset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('80',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','81'])).

thf('83',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['57','82'])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('85',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','86'])).

thf('88',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k8_relset_1 @ X10 @ X11 @ X12 @ X11 )
        = ( k1_relset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('102',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UKeqijnxZ5
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 139 iterations in 0.050s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(d3_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf(t52_tops_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_struct_0 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( l1_struct_0 @ B ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.51                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51                 ( ( k8_relset_1 @
% 0.20/0.51                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                     ( k2_struct_0 @ B ) ) =
% 0.20/0.51                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( l1_struct_0 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( l1_struct_0 @ B ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                    ( v1_funct_2 @
% 0.20/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      C @ 
% 0.20/0.51                      ( k1_zfmisc_1 @
% 0.20/0.51                        ( k2_zfmisc_1 @
% 0.20/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.51                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51                    ( ( k8_relset_1 @
% 0.20/0.51                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                        ( k2_struct_0 @ B ) ) =
% 0.20/0.51                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc5_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.51             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.51          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.51          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | (v1_xboole_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.51  thf(d4_partfun1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (v1_partfun1 @ X20 @ X19)
% 0.20/0.51          | ((k1_relat_1 @ X20) = (X19))
% 0.20/0.51          | ~ (v4_relat_1 @ X20 @ X19)
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X4 @ X5)
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('15', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.20/0.51        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '18'])).
% 0.20/0.51  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.20/0.51         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ 
% 0.20/0.51          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.51          | (v1_partfun1 @ X16 @ X17)
% 0.20/0.51          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | (v1_xboole_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.51         | ((u1_struct_0 @ sk_B) = (k1_xboole_0))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '40'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.51         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.20/0.51         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((((v1_partfun1 @ sk_C @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '29'])).
% 0.20/0.51  thf(cc1_partfun1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X15)))
% 0.20/0.51          | (v1_partfun1 @ X14 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((v1_partfun1 @ sk_C @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('clc', [status(thm)], ['46', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (v1_partfun1 @ X20 @ X19)
% 0.20/0.51          | ((k1_relat_1 @ X20) = (X19))
% 0.20/0.51          | ~ (v4_relat_1 @ X20 @ X19)
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.51         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.20/0.51         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '29'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X4 @ X5)
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.20/0.51         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '67'])).
% 0.20/0.51  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '29'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((((m1_subset_1 @ sk_C @ 
% 0.20/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.20/0.51         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf(t38_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (((k8_relset_1 @ X10 @ X11 @ X12 @ X11)
% 0.20/0.51            = (k1_relset_1 @ X10 @ X11 @ X12))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B))
% 0.20/0.51          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.51          = (k1_relat_1 @ sk_C)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '81'])).
% 0.20/0.51  thf('83', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['57', '82'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.20/0.51       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('85', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.20/0.51  thf('86', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['23', '85'])).
% 0.20/0.51  thf('87', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['21', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['0', '87'])).
% 0.20/0.51  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('90', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ 
% 0.20/0.51         (k1_zfmisc_1 @ 
% 0.20/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup+', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (((k8_relset_1 @ X10 @ X11 @ X12 @ X11)
% 0.20/0.51            = (k1_relset_1 @ X10 @ X11 @ X12))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B))
% 0.20/0.51         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.51         = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['102', '105'])).
% 0.20/0.51  thf('107', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['95', '106'])).
% 0.20/0.51  thf('108', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['90', '107'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
