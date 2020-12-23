%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GsbVLigL4X

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:41 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 444 expanded)
%              Number of leaves         :   48 ( 148 expanded)
%              Depth                    :   21
%              Number of atoms          : 1441 (6016 expanded)
%              Number of equality atoms :  159 ( 538 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
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

thf('3',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( v1_partfun1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ( v1_partfun1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
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
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_partfun1 @ X43 @ X42 )
      | ( ( k1_relat_1 @ X43 )
        = X42 )
      | ~ ( v4_relat_1 @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('37',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('39',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('45',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','46'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('48',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('49',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) @ X20 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('60',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','58','61'])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k10_relat_1 @ X18 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('70',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','71','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('78',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('81',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('82',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('83',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

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
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

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
    inference(split,[status(esa)],['26'])).

thf('92',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

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
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    inference('sup+',[status(thm)],['48','49'])).

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
    inference('sup-',[status(thm)],['76','122'])).

thf('124',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','123'])).

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
    inference(split,[status(esa)],['26'])).

thf('129',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['47','129'])).

thf('131',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('134',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('138',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('142',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B_1 ) ) )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['131','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B_1 ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('147',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','149'])).

thf('151',plain,(
    $false ),
    inference(simplify,[status(thm)],['150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GsbVLigL4X
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.93/3.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.93/3.13  % Solved by: fo/fo7.sh
% 2.93/3.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.93/3.13  % done 3707 iterations in 2.681s
% 2.93/3.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.93/3.13  % SZS output start Refutation
% 2.93/3.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.93/3.13  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.93/3.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.93/3.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.93/3.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.93/3.13  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.93/3.13  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.93/3.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.93/3.13  thf(sk_C_type, type, sk_C: $i).
% 2.93/3.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.93/3.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.93/3.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.93/3.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.93/3.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.93/3.13  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.93/3.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.93/3.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.93/3.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.93/3.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.93/3.13  thf(sk_A_type, type, sk_A: $i).
% 2.93/3.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.93/3.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.93/3.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.93/3.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.93/3.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.93/3.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.93/3.13  thf(d3_struct_0, axiom,
% 2.93/3.13    (![A:$i]:
% 2.93/3.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.93/3.13  thf('0', plain,
% 2.93/3.13      (![X47 : $i]:
% 2.93/3.13         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.13  thf('1', plain,
% 2.93/3.13      (![X47 : $i]:
% 2.93/3.13         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.13  thf(t52_tops_2, conjecture,
% 2.93/3.13    (![A:$i]:
% 2.93/3.13     ( ( l1_struct_0 @ A ) =>
% 2.93/3.13       ( ![B:$i]:
% 2.93/3.13         ( ( l1_struct_0 @ B ) =>
% 2.93/3.13           ( ![C:$i]:
% 2.93/3.13             ( ( ( v1_funct_1 @ C ) & 
% 2.93/3.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.93/3.13                 ( m1_subset_1 @
% 2.93/3.13                   C @ 
% 2.93/3.13                   ( k1_zfmisc_1 @
% 2.93/3.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.93/3.13               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 2.93/3.13                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.93/3.13                 ( ( k8_relset_1 @
% 2.93/3.13                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.93/3.13                     ( k2_struct_0 @ B ) ) =
% 2.93/3.13                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 2.93/3.13  thf(zf_stmt_0, negated_conjecture,
% 2.93/3.13    (~( ![A:$i]:
% 2.93/3.13        ( ( l1_struct_0 @ A ) =>
% 2.93/3.13          ( ![B:$i]:
% 2.93/3.13            ( ( l1_struct_0 @ B ) =>
% 2.93/3.13              ( ![C:$i]:
% 2.93/3.13                ( ( ( v1_funct_1 @ C ) & 
% 2.93/3.13                    ( v1_funct_2 @
% 2.93/3.13                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.93/3.13                    ( m1_subset_1 @
% 2.93/3.13                      C @ 
% 2.93/3.13                      ( k1_zfmisc_1 @
% 2.93/3.13                        ( k2_zfmisc_1 @
% 2.93/3.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.93/3.13                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 2.93/3.13                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.93/3.13                    ( ( k8_relset_1 @
% 2.93/3.13                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.93/3.13                        ( k2_struct_0 @ B ) ) =
% 2.93/3.13                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 2.93/3.13    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 2.93/3.13  thf('2', plain,
% 2.93/3.13      ((m1_subset_1 @ sk_C @ 
% 2.93/3.13        (k1_zfmisc_1 @ 
% 2.93/3.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf(t132_funct_2, axiom,
% 2.93/3.13    (![A:$i,B:$i,C:$i]:
% 2.93/3.13     ( ( ( v1_funct_1 @ C ) & 
% 2.93/3.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.13       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.93/3.13           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.13         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.93/3.13           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.93/3.13  thf('3', plain,
% 2.93/3.13      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.93/3.13         (((X44) = (k1_xboole_0))
% 2.93/3.13          | ~ (v1_funct_1 @ X45)
% 2.93/3.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 2.93/3.13          | (v1_partfun1 @ X45 @ X46)
% 2.93/3.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 2.93/3.13          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 2.93/3.13          | ~ (v1_funct_1 @ X45))),
% 2.93/3.13      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.93/3.13  thf('4', plain,
% 2.93/3.13      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.93/3.13         (~ (v1_funct_2 @ X45 @ X46 @ X44)
% 2.93/3.13          | (v1_partfun1 @ X45 @ X46)
% 2.93/3.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 2.93/3.13          | ~ (v1_funct_1 @ X45)
% 2.93/3.13          | ((X44) = (k1_xboole_0)))),
% 2.93/3.13      inference('simplify', [status(thm)], ['3'])).
% 2.93/3.13  thf('5', plain,
% 2.93/3.13      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.13        | ~ (v1_funct_1 @ sk_C)
% 2.93/3.13        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.93/3.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.13      inference('sup-', [status(thm)], ['2', '4'])).
% 2.93/3.13  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('7', plain,
% 2.93/3.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('8', plain,
% 2.93/3.13      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.13        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.93/3.13      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.93/3.13  thf(d4_partfun1, axiom,
% 2.93/3.13    (![A:$i,B:$i]:
% 2.93/3.13     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.93/3.13       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.93/3.13  thf('9', plain,
% 2.93/3.13      (![X42 : $i, X43 : $i]:
% 2.93/3.13         (~ (v1_partfun1 @ X43 @ X42)
% 2.93/3.13          | ((k1_relat_1 @ X43) = (X42))
% 2.93/3.13          | ~ (v4_relat_1 @ X43 @ X42)
% 2.93/3.13          | ~ (v1_relat_1 @ X43))),
% 2.93/3.13      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.93/3.13  thf('10', plain,
% 2.93/3.13      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.13        | ~ (v1_relat_1 @ sk_C)
% 2.93/3.13        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.93/3.13        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.93/3.13      inference('sup-', [status(thm)], ['8', '9'])).
% 2.93/3.13  thf('11', plain,
% 2.93/3.13      ((m1_subset_1 @ sk_C @ 
% 2.93/3.13        (k1_zfmisc_1 @ 
% 2.93/3.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf(cc2_relat_1, axiom,
% 2.93/3.13    (![A:$i]:
% 2.93/3.13     ( ( v1_relat_1 @ A ) =>
% 2.93/3.13       ( ![B:$i]:
% 2.93/3.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.93/3.13  thf('12', plain,
% 2.93/3.13      (![X6 : $i, X7 : $i]:
% 2.93/3.13         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.93/3.13          | (v1_relat_1 @ X6)
% 2.93/3.13          | ~ (v1_relat_1 @ X7))),
% 2.93/3.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.93/3.13  thf('13', plain,
% 2.93/3.13      ((~ (v1_relat_1 @ 
% 2.93/3.13           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.13        | (v1_relat_1 @ sk_C))),
% 2.93/3.13      inference('sup-', [status(thm)], ['11', '12'])).
% 2.93/3.13  thf(fc6_relat_1, axiom,
% 2.93/3.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.93/3.13  thf('14', plain,
% 2.93/3.13      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.93/3.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.93/3.13  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 2.93/3.13      inference('demod', [status(thm)], ['13', '14'])).
% 2.93/3.13  thf('16', plain,
% 2.93/3.13      ((m1_subset_1 @ sk_C @ 
% 2.93/3.13        (k1_zfmisc_1 @ 
% 2.93/3.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf(cc2_relset_1, axiom,
% 2.93/3.13    (![A:$i,B:$i,C:$i]:
% 2.93/3.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.93/3.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.93/3.13  thf('17', plain,
% 2.93/3.13      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.93/3.13         ((v4_relat_1 @ X29 @ X30)
% 2.93/3.13          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.93/3.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.93/3.13  thf('18', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.93/3.13      inference('sup-', [status(thm)], ['16', '17'])).
% 2.93/3.14  thf('19', plain,
% 2.93/3.14      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.14        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.93/3.14      inference('demod', [status(thm)], ['10', '15', '18'])).
% 2.93/3.14  thf('20', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_B_1)
% 2.93/3.14        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.93/3.14      inference('sup+', [status(thm)], ['1', '19'])).
% 2.93/3.14  thf('21', plain, ((l1_struct_0 @ sk_B_1)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('22', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 2.93/3.14        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.93/3.14      inference('demod', [status(thm)], ['20', '21'])).
% 2.93/3.14  thf('23', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_A)
% 2.93/3.14        | ((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.93/3.14      inference('sup+', [status(thm)], ['0', '22'])).
% 2.93/3.14  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('25', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 2.93/3.14        | ((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.93/3.14      inference('demod', [status(thm)], ['23', '24'])).
% 2.93/3.14  thf('26', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.93/3.14        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('27', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('28', plain,
% 2.93/3.14      (((((k1_xboole_0) != (k1_xboole_0))
% 2.93/3.14         | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['25', '27'])).
% 2.93/3.14  thf('29', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('simplify', [status(thm)], ['28'])).
% 2.93/3.14  thf('30', plain,
% 2.93/3.14      (![X47 : $i]:
% 2.93/3.14         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.14  thf('31', plain,
% 2.93/3.14      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('32', plain,
% 2.93/3.14      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_A))),
% 2.93/3.14      inference('sup-', [status(thm)], ['30', '31'])).
% 2.93/3.14  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('34', plain,
% 2.93/3.14      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.93/3.14      inference('demod', [status(thm)], ['32', '33'])).
% 2.93/3.14  thf('35', plain,
% 2.93/3.14      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['29', '34'])).
% 2.93/3.14  thf('36', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('simplify', [status(thm)], ['28'])).
% 2.93/3.14  thf('37', plain,
% 2.93/3.14      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14          (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['35', '36'])).
% 2.93/3.14  thf('38', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('simplify', [status(thm)], ['28'])).
% 2.93/3.14  thf('39', plain,
% 2.93/3.14      (![X47 : $i]:
% 2.93/3.14         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.14  thf('40', plain,
% 2.93/3.14      ((m1_subset_1 @ sk_C @ 
% 2.93/3.14        (k1_zfmisc_1 @ 
% 2.93/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('41', plain,
% 2.93/3.14      (((m1_subset_1 @ sk_C @ 
% 2.93/3.14         (k1_zfmisc_1 @ 
% 2.93/3.14          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_A))),
% 2.93/3.14      inference('sup+', [status(thm)], ['39', '40'])).
% 2.93/3.14  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('43', plain,
% 2.93/3.14      ((m1_subset_1 @ sk_C @ 
% 2.93/3.14        (k1_zfmisc_1 @ 
% 2.93/3.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.14      inference('demod', [status(thm)], ['41', '42'])).
% 2.93/3.14  thf('44', plain,
% 2.93/3.14      (((m1_subset_1 @ sk_C @ 
% 2.93/3.14         (k1_zfmisc_1 @ 
% 2.93/3.14          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1)))))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup+', [status(thm)], ['38', '43'])).
% 2.93/3.14  thf(redefinition_k8_relset_1, axiom,
% 2.93/3.14    (![A:$i,B:$i,C:$i,D:$i]:
% 2.93/3.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.93/3.14       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.93/3.14  thf('45', plain,
% 2.93/3.14      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.93/3.14         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.93/3.14          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 2.93/3.14      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.93/3.14  thf('46', plain,
% 2.93/3.14      ((![X0 : $i]:
% 2.93/3.14          ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.14            sk_C @ X0) = (k10_relat_1 @ sk_C @ X0)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['44', '45'])).
% 2.93/3.14  thf('47', plain,
% 2.93/3.14      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C)))
% 2.93/3.14         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['37', '46'])).
% 2.93/3.14  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.93/3.14  thf('48', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.93/3.14  thf(t71_relat_1, axiom,
% 2.93/3.14    (![A:$i]:
% 2.93/3.14     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.93/3.14       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.93/3.14  thf('49', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.93/3.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.93/3.14  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['48', '49'])).
% 2.93/3.14  thf(t79_relat_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( v1_relat_1 @ B ) =>
% 2.93/3.14       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.93/3.14         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.93/3.14  thf('51', plain,
% 2.93/3.14      (![X23 : $i, X24 : $i]:
% 2.93/3.14         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 2.93/3.14          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 2.93/3.14          | ~ (v1_relat_1 @ X23))),
% 2.93/3.14      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.93/3.14  thf('52', plain,
% 2.93/3.14      (![X0 : $i]:
% 2.93/3.14         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.93/3.14          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.93/3.14          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 2.93/3.14      inference('sup-', [status(thm)], ['50', '51'])).
% 2.93/3.14  thf(t113_zfmisc_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.93/3.14       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.93/3.14  thf('53', plain,
% 2.93/3.14      (![X3 : $i, X4 : $i]:
% 2.93/3.14         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.93/3.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.93/3.14  thf('54', plain,
% 2.93/3.14      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.93/3.14      inference('simplify', [status(thm)], ['53'])).
% 2.93/3.14  thf(t194_relat_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 2.93/3.14  thf('55', plain,
% 2.93/3.14      (![X19 : $i, X20 : $i]:
% 2.93/3.14         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X19 @ X20)) @ X20)),
% 2.93/3.14      inference('cnf', [status(esa)], [t194_relat_1])).
% 2.93/3.14  thf('56', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.93/3.14      inference('sup+', [status(thm)], ['54', '55'])).
% 2.93/3.14  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['48', '49'])).
% 2.93/3.14  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.93/3.14      inference('demod', [status(thm)], ['56', '57'])).
% 2.93/3.14  thf('59', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.93/3.14  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.93/3.14  thf('60', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.93/3.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.93/3.14  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.93/3.14      inference('sup+', [status(thm)], ['59', '60'])).
% 2.93/3.14  thf('62', plain,
% 2.93/3.14      (![X0 : $i]:
% 2.93/3.14         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 2.93/3.14      inference('demod', [status(thm)], ['52', '58', '61'])).
% 2.93/3.14  thf('63', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.93/3.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.93/3.14  thf(t182_relat_1, axiom,
% 2.93/3.14    (![A:$i]:
% 2.93/3.14     ( ( v1_relat_1 @ A ) =>
% 2.93/3.14       ( ![B:$i]:
% 2.93/3.14         ( ( v1_relat_1 @ B ) =>
% 2.93/3.14           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.93/3.14             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.93/3.14  thf('64', plain,
% 2.93/3.14      (![X17 : $i, X18 : $i]:
% 2.93/3.14         (~ (v1_relat_1 @ X17)
% 2.93/3.14          | ((k1_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.93/3.14              = (k10_relat_1 @ X18 @ (k1_relat_1 @ X17)))
% 2.93/3.14          | ~ (v1_relat_1 @ X18))),
% 2.93/3.14      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.93/3.14  thf('65', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.93/3.14            = (k10_relat_1 @ X1 @ X0))
% 2.93/3.14          | ~ (v1_relat_1 @ X1)
% 2.93/3.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.93/3.14      inference('sup+', [status(thm)], ['63', '64'])).
% 2.93/3.14  thf('66', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 2.93/3.14      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.93/3.14  thf('67', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.93/3.14            = (k10_relat_1 @ X1 @ X0))
% 2.93/3.14          | ~ (v1_relat_1 @ X1))),
% 2.93/3.14      inference('demod', [status(thm)], ['65', '66'])).
% 2.93/3.14  thf('68', plain,
% 2.93/3.14      (![X0 : $i]:
% 2.93/3.14         (((k1_relat_1 @ k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 2.93/3.14          | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['62', '67'])).
% 2.93/3.14  thf('69', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.93/3.14  thf('70', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.93/3.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.93/3.14  thf('71', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['69', '70'])).
% 2.93/3.14  thf('72', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.93/3.14      inference('sup+', [status(thm)], ['59', '60'])).
% 2.93/3.14  thf('73', plain,
% 2.93/3.14      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 2.93/3.14      inference('demod', [status(thm)], ['68', '71', '72'])).
% 2.93/3.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.93/3.14  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.14  thf(t8_boole, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.93/3.14  thf('75', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.93/3.14      inference('cnf', [status(esa)], [t8_boole])).
% 2.93/3.14  thf('76', plain,
% 2.93/3.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.14      inference('sup-', [status(thm)], ['74', '75'])).
% 2.93/3.14  thf('77', plain,
% 2.93/3.14      ((m1_subset_1 @ sk_C @ 
% 2.93/3.14        (k1_zfmisc_1 @ 
% 2.93/3.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.14      inference('demod', [status(thm)], ['41', '42'])).
% 2.93/3.14  thf('78', plain,
% 2.93/3.14      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.93/3.14         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.93/3.14          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 2.93/3.14      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.93/3.14  thf('79', plain,
% 2.93/3.14      (![X0 : $i]:
% 2.93/3.14         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.14           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.93/3.14      inference('sup-', [status(thm)], ['77', '78'])).
% 2.93/3.14  thf('80', plain,
% 2.93/3.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.14      inference('sup-', [status(thm)], ['74', '75'])).
% 2.93/3.14  thf('81', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('82', plain,
% 2.93/3.14      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 2.93/3.14      inference('demod', [status(thm)], ['32', '33'])).
% 2.93/3.14  thf('83', plain,
% 2.93/3.14      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['81', '82'])).
% 2.93/3.14  thf('84', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('85', plain,
% 2.93/3.14      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['83', '84'])).
% 2.93/3.14  thf('86', plain,
% 2.93/3.14      ((![X0 : $i]:
% 2.93/3.14          (((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 2.93/3.14             (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.93/3.14           | ~ (v1_xboole_0 @ X0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['80', '85'])).
% 2.93/3.14  thf('87', plain,
% 2.93/3.14      (((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.93/3.14         | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['79', '86'])).
% 2.93/3.14  thf('88', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.14  thf('90', plain,
% 2.93/3.14      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['87', '88', '89'])).
% 2.93/3.14  thf('91', plain,
% 2.93/3.14      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('92', plain,
% 2.93/3.14      (![X47 : $i]:
% 2.93/3.14         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.14  thf('93', plain,
% 2.93/3.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.14      inference('sup-', [status(thm)], ['74', '75'])).
% 2.93/3.14  thf('94', plain,
% 2.93/3.14      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.93/3.14      inference('simplify', [status(thm)], ['53'])).
% 2.93/3.14  thf('95', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['93', '94'])).
% 2.93/3.14  thf('96', plain,
% 2.93/3.14      ((m1_subset_1 @ sk_C @ 
% 2.93/3.14        (k1_zfmisc_1 @ 
% 2.93/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('97', plain,
% 2.93/3.14      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.93/3.14        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.14      inference('sup+', [status(thm)], ['95', '96'])).
% 2.93/3.14  thf('98', plain,
% 2.93/3.14      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_A)
% 2.93/3.14        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.93/3.14      inference('sup-', [status(thm)], ['92', '97'])).
% 2.93/3.14  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('100', plain,
% 2.93/3.14      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.93/3.14        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.93/3.14      inference('demod', [status(thm)], ['98', '99'])).
% 2.93/3.14  thf('101', plain,
% 2.93/3.14      (((~ (v1_xboole_0 @ k1_xboole_0)
% 2.93/3.14         | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['91', '100'])).
% 2.93/3.14  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.14  thf('103', plain,
% 2.93/3.14      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['101', '102'])).
% 2.93/3.14  thf(t162_funct_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.93/3.14       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 2.93/3.14  thf('104', plain,
% 2.93/3.14      (![X25 : $i, X26 : $i]:
% 2.93/3.14         (((k9_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 2.93/3.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 2.93/3.14      inference('cnf', [status(esa)], [t162_funct_1])).
% 2.93/3.14  thf('105', plain,
% 2.93/3.14      ((((k9_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ sk_C) = (sk_C)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['103', '104'])).
% 2.93/3.14  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.93/3.14  thf('107', plain,
% 2.93/3.14      ((((k9_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['105', '106'])).
% 2.93/3.14  thf(fc17_relat_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) ) =>
% 2.93/3.14       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 2.93/3.14         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 2.93/3.14  thf('108', plain,
% 2.93/3.14      (![X11 : $i, X12 : $i]:
% 2.93/3.14         (~ (v1_relat_1 @ X11)
% 2.93/3.14          | ~ (v1_xboole_0 @ X11)
% 2.93/3.14          | (v1_xboole_0 @ (k7_relat_1 @ X11 @ X12)))),
% 2.93/3.14      inference('cnf', [status(esa)], [fc17_relat_1])).
% 2.93/3.14  thf(cc1_relat_1, axiom,
% 2.93/3.14    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.93/3.14  thf('109', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.93/3.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.93/3.14  thf('110', plain,
% 2.93/3.14      (![X11 : $i, X12 : $i]:
% 2.93/3.14         ((v1_xboole_0 @ (k7_relat_1 @ X11 @ X12)) | ~ (v1_xboole_0 @ X11))),
% 2.93/3.14      inference('clc', [status(thm)], ['108', '109'])).
% 2.93/3.14  thf('111', plain,
% 2.93/3.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.14      inference('sup-', [status(thm)], ['74', '75'])).
% 2.93/3.14  thf('112', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0)))),
% 2.93/3.14      inference('sup-', [status(thm)], ['110', '111'])).
% 2.93/3.14  thf(t148_relat_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( v1_relat_1 @ B ) =>
% 2.93/3.14       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.93/3.14  thf('113', plain,
% 2.93/3.14      (![X15 : $i, X16 : $i]:
% 2.93/3.14         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 2.93/3.14          | ~ (v1_relat_1 @ X15))),
% 2.93/3.14      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.93/3.14  thf('114', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 2.93/3.14          | ~ (v1_xboole_0 @ X1)
% 2.93/3.14          | ~ (v1_relat_1 @ X1))),
% 2.93/3.14      inference('sup+', [status(thm)], ['112', '113'])).
% 2.93/3.14  thf('115', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.14      inference('sup+', [status(thm)], ['48', '49'])).
% 2.93/3.14  thf('116', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 2.93/3.14          | ~ (v1_xboole_0 @ X1)
% 2.93/3.14          | ~ (v1_relat_1 @ X1))),
% 2.93/3.14      inference('demod', [status(thm)], ['114', '115'])).
% 2.93/3.14  thf('117', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.93/3.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.93/3.14  thf('118', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k9_relat_1 @ X1 @ X0)))),
% 2.93/3.14      inference('clc', [status(thm)], ['116', '117'])).
% 2.93/3.14  thf('119', plain,
% 2.93/3.14      (((((k1_xboole_0) = (sk_C)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup+', [status(thm)], ['107', '118'])).
% 2.93/3.14  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.14  thf('121', plain,
% 2.93/3.14      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['119', '120'])).
% 2.93/3.14  thf('122', plain,
% 2.93/3.14      ((((k10_relat_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['90', '121'])).
% 2.93/3.14  thf('123', plain,
% 2.93/3.14      ((![X0 : $i]:
% 2.93/3.14          (((k10_relat_1 @ X0 @ (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 2.93/3.14           | ~ (v1_xboole_0 @ X0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['76', '122'])).
% 2.93/3.14  thf('124', plain,
% 2.93/3.14      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('sup-', [status(thm)], ['73', '123'])).
% 2.93/3.14  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.14  thf('126', plain,
% 2.93/3.14      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.93/3.14         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 2.93/3.14      inference('demod', [status(thm)], ['124', '125'])).
% 2.93/3.14  thf('127', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.93/3.14      inference('simplify', [status(thm)], ['126'])).
% 2.93/3.14  thf('128', plain,
% 2.93/3.14      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 2.93/3.14       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.93/3.14      inference('split', [status(esa)], ['26'])).
% 2.93/3.14  thf('129', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 2.93/3.14      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 2.93/3.14  thf('130', plain,
% 2.93/3.14      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C))),
% 2.93/3.14      inference('simpl_trail', [status(thm)], ['47', '129'])).
% 2.93/3.14  thf('131', plain,
% 2.93/3.14      (![X47 : $i]:
% 2.93/3.14         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 2.93/3.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.93/3.14  thf('132', plain,
% 2.93/3.14      ((m1_subset_1 @ sk_C @ 
% 2.93/3.14        (k1_zfmisc_1 @ 
% 2.93/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('133', plain,
% 2.93/3.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.93/3.14         ((v5_relat_1 @ X29 @ X31)
% 2.93/3.14          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.93/3.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.93/3.14  thf('134', plain, ((v5_relat_1 @ sk_C @ (u1_struct_0 @ sk_B_1))),
% 2.93/3.14      inference('sup-', [status(thm)], ['132', '133'])).
% 2.93/3.14  thf(d19_relat_1, axiom,
% 2.93/3.14    (![A:$i,B:$i]:
% 2.93/3.14     ( ( v1_relat_1 @ B ) =>
% 2.93/3.14       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.93/3.14  thf('135', plain,
% 2.93/3.14      (![X8 : $i, X9 : $i]:
% 2.93/3.14         (~ (v5_relat_1 @ X8 @ X9)
% 2.93/3.14          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 2.93/3.14          | ~ (v1_relat_1 @ X8))),
% 2.93/3.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.93/3.14  thf('136', plain,
% 2.93/3.14      ((~ (v1_relat_1 @ sk_C)
% 2.93/3.14        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.14      inference('sup-', [status(thm)], ['134', '135'])).
% 2.93/3.14  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 2.93/3.14      inference('demod', [status(thm)], ['13', '14'])).
% 2.93/3.14  thf('138', plain,
% 2.93/3.14      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.93/3.14      inference('demod', [status(thm)], ['136', '137'])).
% 2.93/3.14  thf('139', plain,
% 2.93/3.14      (![X23 : $i, X24 : $i]:
% 2.93/3.14         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 2.93/3.14          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 2.93/3.14          | ~ (v1_relat_1 @ X23))),
% 2.93/3.14      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.93/3.14  thf('140', plain,
% 2.93/3.14      ((~ (v1_relat_1 @ sk_C)
% 2.93/3.14        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B_1))) = (sk_C)))),
% 2.93/3.14      inference('sup-', [status(thm)], ['138', '139'])).
% 2.93/3.14  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 2.93/3.14      inference('demod', [status(thm)], ['13', '14'])).
% 2.93/3.14  thf('142', plain,
% 2.93/3.14      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B_1))) = (sk_C))),
% 2.93/3.14      inference('demod', [status(thm)], ['140', '141'])).
% 2.93/3.14  thf('143', plain,
% 2.93/3.14      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_struct_0 @ sk_B_1))) = (sk_C))
% 2.93/3.14        | ~ (l1_struct_0 @ sk_B_1))),
% 2.93/3.14      inference('sup+', [status(thm)], ['131', '142'])).
% 2.93/3.14  thf('144', plain, ((l1_struct_0 @ sk_B_1)),
% 2.93/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.14  thf('145', plain,
% 2.93/3.14      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_struct_0 @ sk_B_1))) = (sk_C))),
% 2.93/3.14      inference('demod', [status(thm)], ['143', '144'])).
% 2.93/3.14  thf('146', plain,
% 2.93/3.14      (![X0 : $i, X1 : $i]:
% 2.93/3.14         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.93/3.14            = (k10_relat_1 @ X1 @ X0))
% 2.93/3.14          | ~ (v1_relat_1 @ X1))),
% 2.93/3.14      inference('demod', [status(thm)], ['65', '66'])).
% 2.93/3.14  thf('147', plain,
% 2.93/3.14      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))
% 2.93/3.14        | ~ (v1_relat_1 @ sk_C))),
% 2.93/3.14      inference('sup+', [status(thm)], ['145', '146'])).
% 2.93/3.14  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 2.93/3.14      inference('demod', [status(thm)], ['13', '14'])).
% 2.93/3.14  thf('149', plain,
% 2.93/3.14      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))),
% 2.93/3.14      inference('demod', [status(thm)], ['147', '148'])).
% 2.93/3.14  thf('150', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 2.93/3.14      inference('demod', [status(thm)], ['130', '149'])).
% 2.93/3.14  thf('151', plain, ($false), inference('simplify', [status(thm)], ['150'])).
% 2.93/3.14  
% 2.93/3.14  % SZS output end Refutation
% 2.93/3.14  
% 2.93/3.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
