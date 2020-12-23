%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9frYZz1x06

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 420 expanded)
%              Number of leaves         :   38 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          : 1137 (7082 expanded)
%              Number of equality atoms :   98 ( 560 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','21','24'])).

thf('26',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('37',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('45',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','44'])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['25','45'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('66',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X6 ) @ X7 )
      | ( ( k10_relat_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','79'])).

thf('81',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('90',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('92',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['80','95'])).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('98',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('101',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('104',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('105',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('107',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','107'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9frYZz1x06
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 249 iterations in 0.178s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(d3_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf(t52_tops_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( l1_struct_0 @ B ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64                 ( ( k8_relset_1 @
% 0.46/0.64                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.64                     ( k2_struct_0 @ B ) ) =
% 0.46/0.64                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( l1_struct_0 @ A ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( l1_struct_0 @ B ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                    ( v1_funct_2 @
% 0.46/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                    ( m1_subset_1 @
% 0.46/0.64                      C @ 
% 0.46/0.64                      ( k1_zfmisc_1 @
% 0.46/0.64                        ( k2_zfmisc_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64                    ( ( k8_relset_1 @
% 0.46/0.64                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.64                        ( k2_struct_0 @ B ) ) =
% 0.46/0.64                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(cc5_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.64          | (v1_partfun1 @ X21 @ X22)
% 0.46/0.64          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.46/0.64          | ~ (v1_funct_1 @ X21)
% 0.46/0.64          | (v1_xboole_0 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.46/0.64  thf(d4_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X25 @ X24)
% 0.46/0.64          | ((k1_relat_1 @ X25) = (X24))
% 0.46/0.64          | ~ (v4_relat_1 @ X25 @ X24)
% 0.46/0.64          | ~ (v1_relat_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.46/0.64          | (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ 
% 0.46/0.64           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.64        | (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf(fc6_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X8 @ X9)
% 0.46/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('24', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '21', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.64          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf(t38_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.46/0.64         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.46/0.64            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.46/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k2_struct_0 @ sk_B))
% 0.46/0.64         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.64          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.46/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['37', '40', '43'])).
% 0.46/0.64  thf('45', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '44'])).
% 0.46/0.64  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['25', '45'])).
% 0.46/0.64  thf(l13_xboole_0, axiom,
% 0.46/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.64  thf('48', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '48'])).
% 0.46/0.64  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('51', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.46/0.64        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.46/0.64         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.64          | (v1_partfun1 @ X21 @ X22)
% 0.46/0.64          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.46/0.64          | ~ (v1_funct_1 @ X21)
% 0.46/0.64          | (v1_xboole_0 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['58', '59', '62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.46/0.64            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.46/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (u1_struct_0 @ sk_B))
% 0.46/0.64         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.46/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67', '70'])).
% 0.46/0.64  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.64  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.64  thf('74', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf(t173_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.64         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         (~ (r1_xboole_0 @ (k2_relat_1 @ X6) @ X7)
% 0.46/0.64          | ((k10_relat_1 @ X6 @ X7) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k10_relat_1 @ sk_C @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['71', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((((v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.46/0.64         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['63', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['37', '40', '43'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.64  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['82', '87'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.64          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.46/0.64            = (k10_relat_1 @ sk_C @ X0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['90', '93'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['81', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['80', '95'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X25 @ X24)
% 0.46/0.64          | ((k1_relat_1 @ X25) = (X24))
% 0.46/0.64          | ~ (v4_relat_1 @ X25 @ X24)
% 0.46/0.64          | ~ (v1_relat_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (((~ (v1_relat_1 @ sk_C)
% 0.46/0.64         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.46/0.64         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.64  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X8 @ X9)
% 0.46/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['98', '99', '102'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.46/0.64         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['81', '94'])).
% 0.46/0.64  thf('105', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.64       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('split', [status(esa)], ['52'])).
% 0.46/0.64  thf('107', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 0.46/0.64  thf('108', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['53', '107'])).
% 0.46/0.64  thf('109', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['51', '108'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
