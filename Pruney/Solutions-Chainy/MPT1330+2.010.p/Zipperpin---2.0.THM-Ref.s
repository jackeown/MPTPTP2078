%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GZ1uRD9oUI

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:42 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 382 expanded)
%              Number of leaves         :   34 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          : 1182 (6566 expanded)
%              Number of equality atoms :  113 ( 550 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','13'])).

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
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('32',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','40'])).

thf('42',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['23','41'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t171_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t171_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('72',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('79',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('86',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['67','87'])).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('90',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('93',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91','94'])).

thf('96',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('99',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('104',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','102','105'])).

thf('107',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','106'])).

thf('108',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['95','107'])).

thf('109',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('110',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','110'])).

thf('112',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GZ1uRD9oUI
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 231 iterations in 0.204s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.67  thf(d3_struct_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf(t52_tops_2, conjecture,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( l1_struct_0 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( l1_struct_0 @ B ) =>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.67                 ( m1_subset_1 @
% 0.47/0.67                   C @ 
% 0.47/0.67                   ( k1_zfmisc_1 @
% 0.47/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.67               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67                 ( ( k8_relset_1 @
% 0.47/0.67                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.47/0.67                     ( k2_struct_0 @ B ) ) =
% 0.47/0.67                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i]:
% 0.47/0.67        ( ( l1_struct_0 @ A ) =>
% 0.47/0.67          ( ![B:$i]:
% 0.47/0.67            ( ( l1_struct_0 @ B ) =>
% 0.47/0.67              ( ![C:$i]:
% 0.47/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.67                    ( v1_funct_2 @
% 0.47/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.67                    ( m1_subset_1 @
% 0.47/0.67                      C @ 
% 0.47/0.67                      ( k1_zfmisc_1 @
% 0.47/0.67                        ( k2_zfmisc_1 @
% 0.47/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.67                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67                    ( ( k8_relset_1 @
% 0.47/0.67                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.47/0.67                        ( k2_struct_0 @ B ) ) =
% 0.47/0.67                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.67  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf(cc5_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.67             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.47/0.67          | (v1_partfun1 @ X18 @ X19)
% 0.47/0.67          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.47/0.67          | ~ (v1_funct_1 @ X18)
% 0.47/0.67          | (v1_xboole_0 @ X20))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.67  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.47/0.67  thf(d4_partfun1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (v1_partfun1 @ X22 @ X21)
% 0.47/0.67          | ((k1_relat_1 @ X22) = (X21))
% 0.47/0.67          | ~ (v4_relat_1 @ X22 @ X21)
% 0.47/0.67          | ~ (v1_relat_1 @ X22))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( v1_relat_1 @ C ) ))).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.67         ((v1_relat_1 @ X2)
% 0.47/0.67          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.67  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf(cc2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.67         ((v4_relat_1 @ X5 @ X6)
% 0.47/0.67          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('22', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k8_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.47/0.67          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '27'])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t38_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.47/0.67         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.67         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 0.47/0.67            = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67         (u1_struct_0 @ sk_B))
% 0.47/0.67         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.47/0.67          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k1_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['29', '37'])).
% 0.47/0.67  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.67  thf('41', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '40'])).
% 0.47/0.67  thf('42', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['23', '41'])).
% 0.47/0.67  thf(l13_xboole_0, axiom,
% 0.47/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.67  thf('44', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['0', '44'])).
% 0.47/0.67  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('47', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.47/0.67        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.47/0.67         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      ((((m1_subset_1 @ sk_C @ 
% 0.47/0.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.47/0.67         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['50', '53'])).
% 0.47/0.67  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.47/0.67          | (v1_partfun1 @ X18 @ X19)
% 0.47/0.67          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.47/0.67          | ~ (v1_funct_1 @ X18)
% 0.47/0.67          | (v1_xboole_0 @ X20))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      ((((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67         | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['61', '62'])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      ((((v1_funct_2 @ sk_C @ k1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['60', '63'])).
% 0.47/0.67  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      ((((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['58', '59', '66'])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.67  thf(t171_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X1 : $i]:
% 0.47/0.67         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [t171_relat_1])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.47/0.67          | ~ (v1_xboole_0 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['68', '69'])).
% 0.47/0.67  thf('71', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X23 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('73', plain,
% 0.47/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.67  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['71', '76'])).
% 0.47/0.67  thf('78', plain,
% 0.47/0.67      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('79', plain,
% 0.47/0.67      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['77', '78'])).
% 0.47/0.67  thf('80', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.67  thf('81', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.47/0.67          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.67  thf('82', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.47/0.67            = (k10_relat_1 @ sk_C @ X0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.67  thf('83', plain,
% 0.47/0.67      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['79', '82'])).
% 0.47/0.67  thf('84', plain,
% 0.47/0.67      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.67         | ~ (v1_relat_1 @ sk_C)
% 0.47/0.67         | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['70', '83'])).
% 0.47/0.67  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('86', plain,
% 0.47/0.67      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.67         | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.67  thf('87', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['86'])).
% 0.47/0.67  thf('88', plain,
% 0.47/0.67      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('clc', [status(thm)], ['67', '87'])).
% 0.47/0.67  thf('89', plain,
% 0.47/0.67      (![X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (v1_partfun1 @ X22 @ X21)
% 0.47/0.67          | ((k1_relat_1 @ X22) = (X21))
% 0.47/0.67          | ~ (v4_relat_1 @ X22 @ X21)
% 0.47/0.67          | ~ (v1_relat_1 @ X22))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.67  thf('90', plain,
% 0.47/0.67      (((~ (v1_relat_1 @ sk_C)
% 0.47/0.67         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.47/0.67         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.67  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('92', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.67  thf('93', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.67         ((v4_relat_1 @ X5 @ X6)
% 0.47/0.67          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('94', plain,
% 0.47/0.67      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.67  thf('95', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['90', '91', '94'])).
% 0.47/0.67  thf('96', plain,
% 0.47/0.67      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['79', '82'])).
% 0.47/0.67  thf('97', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('98', plain,
% 0.47/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.67         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 0.47/0.67            = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.47/0.67  thf('99', plain,
% 0.47/0.67      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67          (k2_struct_0 @ sk_B))
% 0.47/0.67          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.67  thf('100', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('101', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.47/0.67          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.67  thf('102', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          ((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ X0)
% 0.47/0.67            = (k10_relat_1 @ sk_C @ X0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.67  thf('103', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('104', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.47/0.67          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('105', plain,
% 0.47/0.67      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67          = (k1_relat_1 @ sk_C)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['103', '104'])).
% 0.47/0.67  thf('106', plain,
% 0.47/0.67      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['99', '102', '105'])).
% 0.47/0.67  thf('107', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.47/0.67         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['96', '106'])).
% 0.47/0.67  thf('108', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['95', '107'])).
% 0.47/0.67  thf('109', plain,
% 0.47/0.67      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.47/0.67       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.67      inference('split', [status(esa)], ['48'])).
% 0.47/0.67  thf('110', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 0.47/0.67  thf('111', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['49', '110'])).
% 0.47/0.67  thf('112', plain, ($false),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['47', '111'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
