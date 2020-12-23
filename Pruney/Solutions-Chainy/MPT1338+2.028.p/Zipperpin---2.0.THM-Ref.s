%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Tn8D4W81B

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:51 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  284 (1675 expanded)
%              Number of leaves         :   52 ( 514 expanded)
%              Depth                    :   25
%              Number of atoms          : 2655 (41108 expanded)
%              Number of equality atoms :  199 (2148 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X30 ) @ X30 )
        = ( k6_partfun1 @ X29 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X31 @ X29 @ X30 )
       != X29 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X30 ) @ X30 )
        = ( k6_relat_1 @ X29 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X31 @ X29 @ X30 )
       != X29 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('40',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','40','41','50','61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('67',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('77',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','81'])).

thf('83',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('100',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','92','98','99'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('102',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('115',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('121',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('125',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127'])).

thf('129',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','118','119','129'])).

thf('131',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('132',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('133',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('134',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('139',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('140',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','141'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('148',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('149',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('150',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != X23 )
      | ( v1_partfun1 @ X24 @ X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('153',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v4_relat_1 @ X24 @ ( k1_relat_1 @ X24 ) )
      | ( v1_partfun1 @ X24 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('160',plain,(
    v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('164',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('165',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('171',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163','171'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('174',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','172','173'])).

thf('175',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('176',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('177',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('179',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['104'])).

thf('180',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','182'])).

thf('184',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('191',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','191'])).

thf('193',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('194',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','194'])).

thf('196',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','195'])).

thf('197',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('199',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['104'])).

thf('202',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['200','201'])).

thf('203',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['130','202'])).

thf('204',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('205',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('206',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('207',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k8_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k10_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('210',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k8_relset_1 @ X20 @ X21 @ X22 @ X21 )
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','213'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['204','214'])).

thf('216',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('218',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163','171'])).

thf('219',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('221',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['203','221'])).

thf('223',plain,
    ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','222'])).

thf('224',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('226',plain,(
    ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','226'])).

thf('228',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['13','228','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Tn8D4W81B
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.85  % Solved by: fo/fo7.sh
% 0.62/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.85  % done 591 iterations in 0.387s
% 0.62/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.85  % SZS output start Refutation
% 0.62/0.85  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.62/0.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.62/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.62/0.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.62/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.62/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.62/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.62/0.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.62/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.62/0.85  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.62/0.85  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.62/0.85  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.62/0.85  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.85  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.62/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.62/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.62/0.85  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.62/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.62/0.85  thf(t62_tops_2, conjecture,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( l1_struct_0 @ A ) =>
% 0.62/0.85       ( ![B:$i]:
% 0.62/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.62/0.85           ( ![C:$i]:
% 0.62/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.62/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.62/0.85                 ( m1_subset_1 @
% 0.62/0.85                   C @ 
% 0.62/0.85                   ( k1_zfmisc_1 @
% 0.62/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.62/0.85               ( ( ( ( k2_relset_1 @
% 0.62/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.62/0.85                     ( k2_struct_0 @ B ) ) & 
% 0.62/0.85                   ( v2_funct_1 @ C ) ) =>
% 0.62/0.85                 ( ( ( k1_relset_1 @
% 0.62/0.85                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.62/0.85                       ( k2_tops_2 @
% 0.62/0.85                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.62/0.85                     ( k2_struct_0 @ B ) ) & 
% 0.62/0.85                   ( ( k2_relset_1 @
% 0.62/0.85                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.62/0.85                       ( k2_tops_2 @
% 0.62/0.85                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.62/0.85                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.62/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.85    (~( ![A:$i]:
% 0.62/0.85        ( ( l1_struct_0 @ A ) =>
% 0.62/0.85          ( ![B:$i]:
% 0.62/0.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.62/0.85              ( ![C:$i]:
% 0.62/0.85                ( ( ( v1_funct_1 @ C ) & 
% 0.62/0.85                    ( v1_funct_2 @
% 0.62/0.85                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.62/0.85                    ( m1_subset_1 @
% 0.62/0.85                      C @ 
% 0.62/0.85                      ( k1_zfmisc_1 @
% 0.62/0.85                        ( k2_zfmisc_1 @
% 0.62/0.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.62/0.85                  ( ( ( ( k2_relset_1 @
% 0.62/0.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.62/0.85                        ( k2_struct_0 @ B ) ) & 
% 0.62/0.85                      ( v2_funct_1 @ C ) ) =>
% 0.62/0.85                    ( ( ( k1_relset_1 @
% 0.62/0.85                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.62/0.85                          ( k2_tops_2 @
% 0.62/0.85                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.62/0.85                        ( k2_struct_0 @ B ) ) & 
% 0.62/0.85                      ( ( k2_relset_1 @
% 0.62/0.85                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.62/0.85                          ( k2_tops_2 @
% 0.62/0.85                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.62/0.85                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.62/0.85    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.62/0.85  thf('0', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(redefinition_k2_relset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.85       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.62/0.85  thf('1', plain,
% 0.62/0.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.62/0.85         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.62/0.85          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.62/0.85  thf('2', plain,
% 0.62/0.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85         = (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.85  thf('3', plain,
% 0.62/0.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85         = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf(d3_struct_0, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.62/0.85  thf('5', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf(fc2_struct_0, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.62/0.85       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.62/0.85  thf('6', plain,
% 0.62/0.85      (![X34 : $i]:
% 0.62/0.85         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 0.62/0.85          | ~ (l1_struct_0 @ X34)
% 0.62/0.85          | (v2_struct_0 @ X34))),
% 0.62/0.85      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.62/0.85  thf('7', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.62/0.85          | ~ (l1_struct_0 @ X0)
% 0.62/0.85          | (v2_struct_0 @ X0)
% 0.62/0.85          | ~ (l1_struct_0 @ X0))),
% 0.62/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.62/0.85  thf('8', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v2_struct_0 @ X0)
% 0.62/0.85          | ~ (l1_struct_0 @ X0)
% 0.62/0.85          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['7'])).
% 0.62/0.85  thf('9', plain,
% 0.62/0.85      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B)
% 0.62/0.85        | (v2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup-', [status(thm)], ['4', '8'])).
% 0.62/0.85  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('11', plain,
% 0.62/0.85      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.85  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('clc', [status(thm)], ['11', '12'])).
% 0.62/0.85  thf('14', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('15', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('16', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('17', plain,
% 0.62/0.85      (((m1_subset_1 @ sk_C @ 
% 0.62/0.85         (k1_zfmisc_1 @ 
% 0.62/0.85          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.85  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('19', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['17', '18'])).
% 0.62/0.85  thf('20', plain,
% 0.62/0.85      (((m1_subset_1 @ sk_C @ 
% 0.62/0.85         (k1_zfmisc_1 @ 
% 0.62/0.85          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['14', '19'])).
% 0.62/0.85  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('22', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.85  thf('23', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('24', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.62/0.85      inference('demod', [status(thm)], ['22', '23'])).
% 0.62/0.85  thf(t35_funct_2, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.62/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.85       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.62/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.62/0.85           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.62/0.85             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.62/0.85  thf('25', plain,
% 0.62/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.62/0.85         (((X29) = (k1_xboole_0))
% 0.62/0.85          | ~ (v1_funct_1 @ X30)
% 0.62/0.85          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.62/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.62/0.85          | ((k5_relat_1 @ (k2_funct_1 @ X30) @ X30) = (k6_partfun1 @ X29))
% 0.62/0.85          | ~ (v2_funct_1 @ X30)
% 0.62/0.85          | ((k2_relset_1 @ X31 @ X29 @ X30) != (X29)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.62/0.85  thf(redefinition_k6_partfun1, axiom,
% 0.62/0.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.62/0.85  thf('26', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.62/0.85  thf('27', plain,
% 0.62/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.62/0.85         (((X29) = (k1_xboole_0))
% 0.62/0.85          | ~ (v1_funct_1 @ X30)
% 0.62/0.85          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.62/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.62/0.85          | ((k5_relat_1 @ (k2_funct_1 @ X30) @ X30) = (k6_relat_1 @ X29))
% 0.62/0.85          | ~ (v2_funct_1 @ X30)
% 0.62/0.85          | ((k2_relset_1 @ X31 @ X29 @ X30) != (X29)))),
% 0.62/0.85      inference('demod', [status(thm)], ['25', '26'])).
% 0.62/0.85  thf('28', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85          != (k2_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v2_funct_1 @ sk_C)
% 0.62/0.85        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.62/0.85            = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.62/0.85        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.62/0.85        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['24', '27'])).
% 0.62/0.85  thf('29', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('30', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('31', plain,
% 0.62/0.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85         = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('32', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85          = (k2_struct_0 @ sk_B))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup+', [status(thm)], ['30', '31'])).
% 0.62/0.85  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('34', plain,
% 0.62/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85         = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['32', '33'])).
% 0.62/0.85  thf('35', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85          = (k2_struct_0 @ sk_B))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['29', '34'])).
% 0.62/0.85  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('37', plain,
% 0.62/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.62/0.85         = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['35', '36'])).
% 0.62/0.85  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('40', plain,
% 0.62/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85         = (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.62/0.85  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(d9_funct_1, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.85       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.62/0.85  thf('43', plain,
% 0.62/0.85      (![X5 : $i]:
% 0.62/0.85         (~ (v2_funct_1 @ X5)
% 0.62/0.85          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.62/0.85          | ~ (v1_funct_1 @ X5)
% 0.62/0.85          | ~ (v1_relat_1 @ X5))),
% 0.62/0.85      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.62/0.85  thf('44', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v2_funct_1 @ sk_C))),
% 0.62/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.62/0.85  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('46', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.85  thf('47', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(cc1_relset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.85       ( v1_relat_1 @ C ) ))).
% 0.62/0.85  thf('48', plain,
% 0.62/0.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.62/0.85         ((v1_relat_1 @ X7)
% 0.62/0.85          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.62/0.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.62/0.85  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('50', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['46', '49'])).
% 0.62/0.85  thf('51', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('52', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('53', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('54', plain,
% 0.62/0.85      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup+', [status(thm)], ['52', '53'])).
% 0.62/0.85  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('56', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['54', '55'])).
% 0.62/0.85  thf('57', plain,
% 0.62/0.85      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['51', '56'])).
% 0.62/0.85  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('59', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['57', '58'])).
% 0.62/0.85  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('61', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['59', '60'])).
% 0.62/0.85  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('63', plain,
% 0.62/0.85      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.62/0.85        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85            = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.62/0.85        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['28', '40', '41', '50', '61', '62'])).
% 0.62/0.85  thf('64', plain,
% 0.62/0.85      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.62/0.85        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85            = (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.62/0.85      inference('simplify', [status(thm)], ['63'])).
% 0.62/0.85  thf(t182_relat_1, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( v1_relat_1 @ A ) =>
% 0.62/0.85       ( ![B:$i]:
% 0.62/0.85         ( ( v1_relat_1 @ B ) =>
% 0.62/0.85           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.62/0.85             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.62/0.85  thf('65', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.62/0.85              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.62/0.85          | ~ (v1_relat_1 @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.62/0.85  thf('66', plain,
% 0.62/0.85      ((((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.62/0.85          = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.62/0.85        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.62/0.85        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.62/0.85      inference('sup+', [status(thm)], ['64', '65'])).
% 0.62/0.85  thf(t71_relat_1, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.62/0.85       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.62/0.85  thf('67', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.62/0.85      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.85  thf('68', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('69', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(t132_funct_2, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( ( v1_funct_1 @ C ) & 
% 0.62/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.85       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.62/0.85           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.62/0.85           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.62/0.85  thf('70', plain,
% 0.62/0.85      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.62/0.85         (((X26) = (k1_xboole_0))
% 0.62/0.85          | ~ (v1_funct_1 @ X27)
% 0.62/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.62/0.85          | (v1_partfun1 @ X27 @ X28)
% 0.62/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.62/0.85          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.62/0.85          | ~ (v1_funct_1 @ X27))),
% 0.62/0.85      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.62/0.85  thf('71', plain,
% 0.62/0.85      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.62/0.85         (~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.62/0.85          | (v1_partfun1 @ X27 @ X28)
% 0.62/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.62/0.85          | ~ (v1_funct_1 @ X27)
% 0.62/0.85          | ((X26) = (k1_xboole_0)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['70'])).
% 0.62/0.85  thf('72', plain,
% 0.62/0.85      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.62/0.85        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.62/0.85        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['69', '71'])).
% 0.62/0.85  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('74', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('75', plain,
% 0.62/0.85      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.62/0.85  thf(d4_partfun1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.62/0.85       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.62/0.85  thf('76', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         (~ (v1_partfun1 @ X24 @ X23)
% 0.62/0.85          | ((k1_relat_1 @ X24) = (X23))
% 0.62/0.85          | ~ (v4_relat_1 @ X24 @ X23)
% 0.62/0.85          | ~ (v1_relat_1 @ X24))),
% 0.62/0.85      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.62/0.85  thf('77', plain,
% 0.62/0.85      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['75', '76'])).
% 0.62/0.85  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('79', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(cc2_relset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.85       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.62/0.85  thf('80', plain,
% 0.62/0.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.62/0.85         ((v4_relat_1 @ X10 @ X11)
% 0.62/0.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.62/0.85      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.85  thf('81', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['79', '80'])).
% 0.62/0.85  thf('82', plain,
% 0.62/0.85      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['77', '78', '81'])).
% 0.62/0.85  thf('83', plain,
% 0.62/0.85      (![X34 : $i]:
% 0.62/0.85         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 0.62/0.85          | ~ (l1_struct_0 @ X34)
% 0.62/0.85          | (v2_struct_0 @ X34))),
% 0.62/0.85      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.62/0.85  thf('84', plain,
% 0.62/0.85      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.62/0.85        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.62/0.85        | (v2_struct_0 @ sk_B)
% 0.62/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup-', [status(thm)], ['82', '83'])).
% 0.62/0.85  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.62/0.85  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.85  thf('86', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('87', plain,
% 0.62/0.85      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.62/0.85      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.62/0.85  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('89', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('clc', [status(thm)], ['87', '88'])).
% 0.62/0.85  thf('90', plain,
% 0.62/0.85      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup+', [status(thm)], ['68', '89'])).
% 0.62/0.85  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('93', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['46', '49'])).
% 0.62/0.85  thf(dt_k2_funct_1, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.85       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.62/0.85         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.62/0.85  thf('94', plain,
% 0.62/0.85      (![X6 : $i]:
% 0.62/0.85         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.62/0.85          | ~ (v1_funct_1 @ X6)
% 0.62/0.85          | ~ (v1_relat_1 @ X6))),
% 0.62/0.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.62/0.85  thf('95', plain,
% 0.62/0.85      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ~ (v1_funct_1 @ sk_C))),
% 0.62/0.85      inference('sup+', [status(thm)], ['93', '94'])).
% 0.62/0.85  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('98', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('100', plain,
% 0.62/0.85      ((((k2_relat_1 @ sk_C)
% 0.62/0.85          = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 0.62/0.85        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['66', '67', '92', '98', '99'])).
% 0.62/0.85  thf(t37_relat_1, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( v1_relat_1 @ A ) =>
% 0.62/0.85       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.62/0.85         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.62/0.85  thf('101', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf('102', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('103', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('104', plain,
% 0.62/0.85      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_B))
% 0.62/0.85        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85            != (k2_struct_0 @ sk_A)))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('105', plain,
% 0.62/0.85      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('split', [status(esa)], ['104'])).
% 0.62/0.85  thf('106', plain,
% 0.62/0.85      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85           != (k2_struct_0 @ sk_B))
% 0.62/0.85         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['103', '105'])).
% 0.62/0.85  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('108', plain,
% 0.62/0.85      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['106', '107'])).
% 0.62/0.85  thf('109', plain,
% 0.62/0.85      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85           != (k2_struct_0 @ sk_B))
% 0.62/0.85         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['102', '108'])).
% 0.62/0.85  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('111', plain,
% 0.62/0.85      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['109', '110'])).
% 0.62/0.85  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('115', plain,
% 0.62/0.85      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.62/0.85          != (k2_relat_1 @ sk_C)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.62/0.85  thf('116', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('clc', [status(thm)], ['87', '88'])).
% 0.62/0.85  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('118', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.62/0.85  thf('119', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.62/0.85  thf('120', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_C @ 
% 0.62/0.85        (k1_zfmisc_1 @ 
% 0.62/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.62/0.85      inference('demod', [status(thm)], ['22', '23'])).
% 0.62/0.85  thf(d4_tops_2, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.62/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.85       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.62/0.85         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.62/0.85  thf('121', plain,
% 0.62/0.85      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.62/0.85         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.62/0.85          | ~ (v2_funct_1 @ X37)
% 0.62/0.85          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.62/0.85          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.62/0.85          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.62/0.85          | ~ (v1_funct_1 @ X37))),
% 0.62/0.85      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.62/0.85  thf('122', plain,
% 0.62/0.85      ((~ (v1_funct_1 @ sk_C)
% 0.62/0.85        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.62/0.85        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85            = (k2_funct_1 @ sk_C))
% 0.62/0.85        | ~ (v2_funct_1 @ sk_C)
% 0.62/0.85        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85            != (k2_relat_1 @ sk_C)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['120', '121'])).
% 0.62/0.85  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('124', plain,
% 0.62/0.85      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['59', '60'])).
% 0.62/0.85  thf('125', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['46', '49'])).
% 0.62/0.85  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('127', plain,
% 0.62/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85         = (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.62/0.85  thf('128', plain,
% 0.62/0.85      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85          = (k4_relat_1 @ sk_C))
% 0.62/0.85        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)],
% 0.62/0.85                ['122', '123', '124', '125', '126', '127'])).
% 0.62/0.85  thf('129', plain,
% 0.62/0.85      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85         = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('simplify', [status(thm)], ['128'])).
% 0.62/0.85  thf('130', plain,
% 0.62/0.85      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.62/0.85          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_B))))),
% 0.62/0.85      inference('demod', [status(thm)], ['115', '118', '119', '129'])).
% 0.62/0.85  thf('131', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf('132', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['46', '49'])).
% 0.62/0.85  thf('133', plain,
% 0.62/0.85      (![X6 : $i]:
% 0.62/0.85         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.62/0.85          | ~ (v1_funct_1 @ X6)
% 0.62/0.85          | ~ (v1_relat_1 @ X6))),
% 0.62/0.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.62/0.85  thf('134', plain,
% 0.62/0.85      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ~ (v1_funct_1 @ sk_C))),
% 0.62/0.85      inference('sup+', [status(thm)], ['132', '133'])).
% 0.62/0.85  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('137', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.62/0.85  thf('138', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf(t3_funct_2, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.85       ( ( v1_funct_1 @ A ) & 
% 0.62/0.85         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.62/0.85         ( m1_subset_1 @
% 0.62/0.85           A @ 
% 0.62/0.85           ( k1_zfmisc_1 @
% 0.62/0.85             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.62/0.85  thf('139', plain,
% 0.62/0.85      (![X32 : $i]:
% 0.62/0.85         ((m1_subset_1 @ X32 @ 
% 0.62/0.85           (k1_zfmisc_1 @ 
% 0.62/0.85            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.62/0.85          | ~ (v1_funct_1 @ X32)
% 0.62/0.85          | ~ (v1_relat_1 @ X32))),
% 0.62/0.85      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.62/0.85  thf('140', plain,
% 0.62/0.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.62/0.85         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.62/0.85          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.62/0.85  thf('141', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.62/0.85              = (k2_relat_1 @ X0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['139', '140'])).
% 0.62/0.85  thf('142', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (((k2_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 0.62/0.85            (k1_relat_1 @ X0) @ (k4_relat_1 @ X0))
% 0.62/0.85            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['138', '141'])).
% 0.62/0.85  thf('143', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ((k2_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.62/0.85            (k1_relat_1 @ sk_C) @ (k4_relat_1 @ sk_C))
% 0.62/0.85            = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['137', '142'])).
% 0.62/0.85  thf('144', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('146', plain,
% 0.62/0.85      (((k2_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.62/0.85         (k1_relat_1 @ sk_C) @ (k4_relat_1 @ sk_C))
% 0.62/0.85         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.62/0.85  thf('147', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.62/0.85  thf('148', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf('149', plain,
% 0.62/0.85      (![X32 : $i]:
% 0.62/0.85         ((m1_subset_1 @ X32 @ 
% 0.62/0.85           (k1_zfmisc_1 @ 
% 0.62/0.85            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.62/0.85          | ~ (v1_funct_1 @ X32)
% 0.62/0.85          | ~ (v1_relat_1 @ X32))),
% 0.62/0.85      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.62/0.85  thf('150', plain,
% 0.62/0.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.62/0.85         ((v4_relat_1 @ X10 @ X11)
% 0.62/0.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.62/0.85      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.85  thf('151', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['149', '150'])).
% 0.62/0.85  thf('152', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         (((k1_relat_1 @ X24) != (X23))
% 0.62/0.85          | (v1_partfun1 @ X24 @ X23)
% 0.62/0.85          | ~ (v4_relat_1 @ X24 @ X23)
% 0.62/0.85          | ~ (v1_relat_1 @ X24))),
% 0.62/0.85      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.62/0.85  thf('153', plain,
% 0.62/0.85      (![X24 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X24)
% 0.62/0.85          | ~ (v4_relat_1 @ X24 @ (k1_relat_1 @ X24))
% 0.62/0.85          | (v1_partfun1 @ X24 @ (k1_relat_1 @ X24)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['152'])).
% 0.62/0.85  thf('154', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_funct_1 @ X0)
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ X0))),
% 0.62/0.85      inference('sup-', [status(thm)], ['151', '153'])).
% 0.62/0.85  thf('155', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0))),
% 0.62/0.85      inference('simplify', [status(thm)], ['154'])).
% 0.62/0.85  thf('156', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v1_partfun1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['148', '155'])).
% 0.62/0.85  thf('157', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['147', '156'])).
% 0.62/0.85  thf('158', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('160', plain,
% 0.62/0.85      ((v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.62/0.85  thf('161', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         (~ (v1_partfun1 @ X24 @ X23)
% 0.62/0.85          | ((k1_relat_1 @ X24) = (X23))
% 0.62/0.85          | ~ (v4_relat_1 @ X24 @ X23)
% 0.62/0.85          | ~ (v1_relat_1 @ X24))),
% 0.62/0.85      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.62/0.85  thf('162', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.62/0.85        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['160', '161'])).
% 0.62/0.85  thf('163', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('164', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.62/0.85  thf('165', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf('166', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['149', '150'])).
% 0.62/0.85  thf('167', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['165', '166'])).
% 0.62/0.85  thf('168', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['164', '167'])).
% 0.62/0.85  thf('169', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('171', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.62/0.85  thf('172', plain,
% 0.62/0.85      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['162', '163', '171'])).
% 0.62/0.85  thf('173', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('174', plain,
% 0.62/0.85      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.62/0.85         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)], ['146', '172', '173'])).
% 0.62/0.85  thf('175', plain,
% 0.62/0.85      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.62/0.85         = (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('simplify', [status(thm)], ['128'])).
% 0.62/0.85  thf('176', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('177', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('178', plain,
% 0.62/0.85      (![X33 : $i]:
% 0.62/0.85         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.62/0.85  thf('179', plain,
% 0.62/0.85      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('split', [status(esa)], ['104'])).
% 0.62/0.85  thf('180', plain,
% 0.62/0.85      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85           != (k2_struct_0 @ sk_A))
% 0.62/0.85         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['178', '179'])).
% 0.62/0.85  thf('181', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('182', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['180', '181'])).
% 0.62/0.85  thf('183', plain,
% 0.62/0.85      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85           != (k2_struct_0 @ sk_A))
% 0.62/0.85         | ~ (l1_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['177', '182'])).
% 0.62/0.85  thf('184', plain, ((l1_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('185', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['183', '184'])).
% 0.62/0.85  thf('186', plain,
% 0.62/0.85      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85           != (k2_struct_0 @ sk_A))
% 0.62/0.85         | ~ (l1_struct_0 @ sk_B)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['176', '185'])).
% 0.62/0.85  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('188', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['186', '187'])).
% 0.62/0.85  thf('189', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('190', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('191', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.62/0.85          != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['188', '189', '190'])).
% 0.62/0.85  thf('192', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['175', '191'])).
% 0.62/0.85  thf('193', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.62/0.85  thf('194', plain,
% 0.62/0.85      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.62/0.85          (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['192', '193'])).
% 0.62/0.85  thf('195', plain,
% 0.62/0.85      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['174', '194'])).
% 0.62/0.85  thf('196', plain,
% 0.62/0.85      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)) | ~ (v1_relat_1 @ sk_C)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['131', '195'])).
% 0.62/0.85  thf('197', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('199', plain,
% 0.62/0.85      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.62/0.85         <= (~
% 0.62/0.85             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85                = (k2_struct_0 @ sk_A))))),
% 0.62/0.85      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.62/0.85  thf('200', plain,
% 0.62/0.85      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          = (k2_struct_0 @ sk_A)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['199'])).
% 0.62/0.85  thf('201', plain,
% 0.62/0.85      (~
% 0.62/0.85       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          = (k2_struct_0 @ sk_B))) | 
% 0.62/0.85       ~
% 0.62/0.85       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          = (k2_struct_0 @ sk_A)))),
% 0.62/0.85      inference('split', [status(esa)], ['104'])).
% 0.62/0.85  thf('202', plain,
% 0.62/0.85      (~
% 0.62/0.85       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.62/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.62/0.85          = (k2_struct_0 @ sk_B)))),
% 0.62/0.85      inference('sat_resolution*', [status(thm)], ['200', '201'])).
% 0.62/0.85  thf('203', plain,
% 0.62/0.85      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.62/0.85         (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('simpl_trail', [status(thm)], ['130', '202'])).
% 0.62/0.85  thf('204', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.62/0.85  thf('205', plain,
% 0.62/0.85      (![X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.62/0.85          | ~ (v1_relat_1 @ X2))),
% 0.62/0.85      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.62/0.85  thf('206', plain,
% 0.62/0.85      (![X32 : $i]:
% 0.62/0.85         ((m1_subset_1 @ X32 @ 
% 0.62/0.85           (k1_zfmisc_1 @ 
% 0.62/0.85            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.62/0.85          | ~ (v1_funct_1 @ X32)
% 0.62/0.85          | ~ (v1_relat_1 @ X32))),
% 0.62/0.85      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.62/0.85  thf(redefinition_k8_relset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.85       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.62/0.85  thf('207', plain,
% 0.62/0.85      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.62/0.85          | ((k8_relset_1 @ X17 @ X18 @ X16 @ X19) = (k10_relat_1 @ X16 @ X19)))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.62/0.85  thf('208', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.62/0.85              = (k10_relat_1 @ X0 @ X1)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['206', '207'])).
% 0.62/0.85  thf('209', plain,
% 0.62/0.85      (![X32 : $i]:
% 0.62/0.85         ((m1_subset_1 @ X32 @ 
% 0.62/0.85           (k1_zfmisc_1 @ 
% 0.62/0.85            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.62/0.85          | ~ (v1_funct_1 @ X32)
% 0.62/0.85          | ~ (v1_relat_1 @ X32))),
% 0.62/0.85      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.62/0.85  thf(t38_relset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.85       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.62/0.85         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.62/0.85  thf('210', plain,
% 0.62/0.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.62/0.85         (((k8_relset_1 @ X20 @ X21 @ X22 @ X21)
% 0.62/0.85            = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.62/0.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.62/0.85      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.62/0.85  thf('211', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ 
% 0.62/0.85              (k2_relat_1 @ X0))
% 0.62/0.85              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['209', '210'])).
% 0.62/0.85  thf('212', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.62/0.85            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ~ (v1_relat_1 @ X0))),
% 0.62/0.85      inference('sup+', [status(thm)], ['208', '211'])).
% 0.62/0.85  thf('213', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ X0)
% 0.62/0.85          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.62/0.85              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['212'])).
% 0.62/0.85  thf('214', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.62/0.85            = (k1_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 0.62/0.85               (k1_relat_1 @ X0) @ (k4_relat_1 @ X0)))
% 0.62/0.85          | ~ (v1_relat_1 @ X0)
% 0.62/0.85          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.62/0.85          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['205', '213'])).
% 0.62/0.85  thf('215', plain,
% 0.62/0.85      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.62/0.85        | ((k10_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 0.62/0.85            (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.62/0.85            = (k1_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.62/0.85               (k1_relat_1 @ sk_C) @ (k4_relat_1 @ sk_C))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['204', '214'])).
% 0.62/0.85  thf('216', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.62/0.85  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('218', plain,
% 0.62/0.85      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['162', '163', '171'])).
% 0.62/0.85  thf('219', plain,
% 0.62/0.85      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.62/0.85         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.62/0.85            (k4_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.62/0.85  thf('220', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('221', plain,
% 0.62/0.85      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.62/0.85         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.62/0.85            (k4_relat_1 @ sk_C)))),
% 0.62/0.85      inference('demod', [status(thm)], ['219', '220'])).
% 0.62/0.85  thf('222', plain,
% 0.62/0.85      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.62/0.85         != (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['203', '221'])).
% 0.62/0.85  thf('223', plain,
% 0.62/0.85      ((((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.62/0.85          != (k2_relat_1 @ sk_C))
% 0.62/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.62/0.85      inference('sup-', [status(thm)], ['101', '222'])).
% 0.62/0.85  thf('224', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['90', '91'])).
% 0.62/0.85  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('226', plain,
% 0.62/0.85      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 0.62/0.85         != (k2_relat_1 @ sk_C))),
% 0.62/0.85      inference('demod', [status(thm)], ['223', '224', '225'])).
% 0.62/0.85  thf('227', plain,
% 0.62/0.85      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.62/0.85        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['100', '226'])).
% 0.62/0.85  thf('228', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.62/0.85      inference('simplify', [status(thm)], ['227'])).
% 0.62/0.85  thf('229', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.85  thf('230', plain, ($false),
% 0.62/0.85      inference('demod', [status(thm)], ['13', '228', '229'])).
% 0.62/0.85  
% 0.62/0.85  % SZS output end Refutation
% 0.62/0.85  
% 0.62/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
