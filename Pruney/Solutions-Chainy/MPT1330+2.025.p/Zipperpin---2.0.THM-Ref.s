%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DXDH3Lac2I

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 548 expanded)
%              Number of leaves         :   42 ( 176 expanded)
%              Depth                    :   22
%              Number of atoms          : 1382 (7689 expanded)
%              Number of equality atoms :  143 ( 620 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_C @ X0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C @ X0 )
          = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v5_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('50',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('54',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('58',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('59',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('61',plain,
    ( ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','62','63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 )
        = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','65'])).

thf('67',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('70',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','77'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('87',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v5_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('101',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('105',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('107',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','90','107'])).

thf('109',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('111',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','111'])).

thf('113',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['118','119'])).

thf('121',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['66','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','111'])).

thf('124',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('126',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k8_relset_1 @ X33 @ X33 @ ( k6_partfun1 @ X33 ) @ X32 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('127',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k8_relset_1 @ X33 @ X33 @ ( k6_relat_1 @ X33 ) @ X32 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['125','128'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('130',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('131',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('132',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('134',plain,(
    ! [X18: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['129','130','135'])).

thf('137',plain,(
    ! [X18: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('138',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('139',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('141',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('142',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['121','136','143'])).

thf('145',plain,(
    $false ),
    inference(simplify,[status(thm)],['144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DXDH3Lac2I
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 164 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(t52_tops_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( l1_struct_0 @ B ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.52                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52                 ( ( k8_relset_1 @
% 0.20/0.52                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.52                     ( k2_struct_0 @ B ) ) =
% 0.20/0.52                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_struct_0 @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( l1_struct_0 @ B ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                    ( v1_funct_2 @
% 0.20/0.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                    ( m1_subset_1 @
% 0.20/0.52                      C @ 
% 0.20/0.52                      ( k1_zfmisc_1 @
% 0.20/0.52                        ( k2_zfmisc_1 @
% 0.20/0.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.52                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52                    ( ( k8_relset_1 @
% 0.20/0.52                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.52                        ( k2_struct_0 @ B ) ) =
% 0.20/0.52                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X34 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.20/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X34 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_C @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_C @ 
% 0.20/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '15'])).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.52          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.52          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.20/0.52              = (k10_relat_1 @ X1 @ X2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]:
% 0.20/0.52          ((k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0)
% 0.20/0.52            = (k10_relat_1 @ sk_C @ X0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf(cc2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         ((v5_relat_1 @ X19 @ X21)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.52          | (v5_relat_1 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((![X0 : $i]: (v5_relat_1 @ sk_C @ X0))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.52  thf(d19_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v5_relat_1 @ X11 @ X12)
% 0.20/0.52          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)))
% 0.20/0.52         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.53          | (v1_relat_1 @ X9)
% 0.20/0.53          | ~ (v1_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ 
% 0.20/0.53           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.20/0.53        | (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0) = (k2_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf(t168_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k10_relat_1 @ B @ A ) =
% 0.20/0.53         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X15 @ X16)
% 0.20/0.53            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k10_relat_1 @ sk_C @ X0)
% 0.20/0.53             = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53           | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '18'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((v5_relat_1 @ X19 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.53          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((v5_relat_1 @ sk_C @ k1_xboole_0))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (v5_relat_1 @ X11 @ X12)
% 0.20/0.53          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | (r1_tarski @ (k2_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r1_tarski @ (k2_relat_1 @ sk_C) @ k1_xboole_0))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ k1_xboole_0)
% 0.20/0.53          = (k2_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X15 @ X16)
% 0.20/0.53            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (((((k10_relat_1 @ sk_C @ k1_xboole_0)
% 0.20/0.53           = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ k1_xboole_0)
% 0.20/0.53          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf(t169_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.20/0.53          | ~ (v1_relat_1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ k1_xboole_0)
% 0.20/0.53          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_relat_1 @ sk_C))
% 0.20/0.53         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['56', '61'])).
% 0.20/0.53  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((![X0 : $i]: ((k10_relat_1 @ sk_C @ X0) = (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) = (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X34 : $i]:
% 0.20/0.53         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t132_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.53           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (((X29) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.20/0.53          | (v1_partfun1 @ X30 @ X31)
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.20/0.53          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.20/0.53          | ~ (v1_funct_1 @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.20/0.53          | (v1_partfun1 @ X30 @ X31)
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ((X29) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.53  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X34 : $i]:
% 0.20/0.53         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.53  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['71', '72', '77'])).
% 0.20/0.53  thf(d4_partfun1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i]:
% 0.20/0.53         (~ (v1_partfun1 @ X27 @ X26)
% 0.20/0.53          | ((k1_relat_1 @ X27) = (X26))
% 0.20/0.53          | ~ (v4_relat_1 @ X27 @ X26)
% 0.20/0.53          | ~ (v1_relat_1 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.20/0.53        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X19 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('84', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.20/0.53          | ~ (v1_relat_1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.53          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (![X34 : $i]:
% 0.20/0.53         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_C @ 
% 0.20/0.53         (k1_zfmisc_1 @ 
% 0.20/0.53          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((v5_relat_1 @ X19 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('97', plain, ((v5_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (v5_relat_1 @ X11 @ X12)
% 0.20/0.53          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('101', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.20/0.53         = (k2_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X15 @ X16)
% 0.20/0.53            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 0.20/0.53          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 0.20/0.53         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['87', '90', '107'])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '108'])).
% 0.20/0.53  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('111', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['109', '110'])).
% 0.20/0.53  thf('112', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['85', '111'])).
% 0.20/0.53  thf('113', plain,
% 0.20/0.53      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['67', '112'])).
% 0.20/0.53  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('115', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['113', '114'])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('117', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.53  thf('118', plain, ((((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['117'])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('120', plain, ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['118', '119'])).
% 0.20/0.53  thf('121', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['66', '120'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('123', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['85', '111'])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('125', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.20/0.53  thf(t171_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         (((k8_relset_1 @ X33 @ X33 @ (k6_partfun1 @ X33) @ X32) = (X32))
% 0.20/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t171_funct_2])).
% 0.20/0.53  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.53  thf('127', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         (((k8_relset_1 @ X33 @ X33 @ (k6_relat_1 @ X33) @ X32) = (X32))
% 0.20/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.20/0.53      inference('demod', [status(thm)], ['126', '127'])).
% 0.20/0.53  thf('129', plain,
% 0.20/0.53      (((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53         (k6_relat_1 @ k1_xboole_0) @ sk_C) = (sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['125', '128'])).
% 0.20/0.53  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.53  thf('130', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.53  thf(t4_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('131', plain,
% 0.20/0.53      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf('132', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.53          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.53  thf('133', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.20/0.53           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.53  thf(t172_relat_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('134', plain,
% 0.20/0.53      (![X18 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.20/0.53  thf('135', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['133', '134'])).
% 0.20/0.53  thf('136', plain, (((k1_xboole_0) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['129', '130', '135'])).
% 0.20/0.53  thf('137', plain,
% 0.20/0.53      (![X18 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.20/0.53  thf('138', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.20/0.53          | ~ (v1_relat_1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.53  thf('139', plain,
% 0.20/0.53      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.20/0.53        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['137', '138'])).
% 0.20/0.53  thf('140', plain,
% 0.20/0.53      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('141', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('142', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['140', '141'])).
% 0.20/0.53  thf('143', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['139', '142'])).
% 0.20/0.53  thf('144', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['121', '136', '143'])).
% 0.20/0.53  thf('145', plain, ($false), inference('simplify', [status(thm)], ['144'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
