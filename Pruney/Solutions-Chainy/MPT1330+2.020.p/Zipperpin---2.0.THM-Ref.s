%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ta9o2H2BG

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  180 (1558 expanded)
%              Number of leaves         :   35 ( 440 expanded)
%              Depth                    :   22
%              Number of atoms          : 1468 (27682 expanded)
%              Number of equality atoms :  140 (2344 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','26','29'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('46',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t171_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t171_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('53',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('64',plain,
    ( ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('67',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('74',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('80',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('84',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','89'])).

thf('91',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['47','90'])).

thf('92',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('93',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('96',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('97',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('100',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('102',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['100','101'])).

thf('103',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','104'])).

thf('106',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('107',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('109',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('110',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','103'])).

thf('112',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','103'])).

thf('120',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('133',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('136',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['121','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','102'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['139','140'])).

thf('142',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','141'])).

thf('143',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['113','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ta9o2H2BG
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 291 iterations in 0.190s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.65  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(d3_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf(t52_tops_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( l1_struct_0 @ B ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.65                 ( m1_subset_1 @
% 0.46/0.65                   C @ 
% 0.46/0.65                   ( k1_zfmisc_1 @
% 0.46/0.65                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.65               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65                 ( ( k8_relset_1 @
% 0.46/0.65                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.65                     ( k2_struct_0 @ B ) ) =
% 0.46/0.65                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( l1_struct_0 @ A ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( l1_struct_0 @ B ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65                    ( v1_funct_2 @
% 0.46/0.65                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.65                    ( m1_subset_1 @
% 0.46/0.65                      C @ 
% 0.46/0.65                      ( k1_zfmisc_1 @
% 0.46/0.65                        ( k2_zfmisc_1 @
% 0.46/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.65                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65                    ( ( k8_relset_1 @
% 0.46/0.65                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.65                        ( k2_struct_0 @ B ) ) =
% 0.46/0.65                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['0', '5'])).
% 0.46/0.65  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf(cc5_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.65          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.65          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.65          | ~ (v1_funct_1 @ X19)
% 0.46/0.65          | (v1_xboole_0 @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13', '18'])).
% 0.46/0.65  thf(d4_partfun1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X23 @ X22)
% 0.46/0.65          | ((k1_relat_1 @ X23) = (X22))
% 0.46/0.65          | ~ (v4_relat_1 @ X23 @ X22)
% 0.46/0.65          | ~ (v1_relat_1 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc2_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.46/0.65          | (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ 
% 0.46/0.65           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.65        | (v1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf(fc6_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.65  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf(cc2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('29', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '26', '29'])).
% 0.46/0.65  thf(l13_xboole_0, axiom,
% 0.46/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.46/0.65        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '32'])).
% 0.46/0.65  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.46/0.65        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.65          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.65          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.65          | ~ (v1_funct_1 @ X19)
% 0.46/0.65          | (v1_xboole_0 @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf(t171_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X5 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [t171_relat_1])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf(t38_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.46/0.65         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 0.46/0.65            = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (u1_struct_0 @ sk_B))
% 0.46/0.65          = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.46/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      ((((k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65          = (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.65          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.46/0.65            = (k10_relat_1 @ sk_C @ X0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['57', '60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (((((k1_xboole_0) = (k1_relat_1 @ sk_C))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['50', '61'])).
% 0.46/0.65  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (((((k1_xboole_0) = (k1_relat_1 @ sk_C))
% 0.46/0.65         | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['66', '71'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.46/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['65', '74'])).
% 0.46/0.65  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      ((((m1_subset_1 @ sk_C @ 
% 0.46/0.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.46/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['78', '79'])).
% 0.46/0.65  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 0.46/0.65            = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B))
% 0.46/0.65          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.46/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65          = (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['84', '87'])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['77', '88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['64', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (((v1_partfun1 @ sk_C @ k1_xboole_0))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('clc', [status(thm)], ['47', '90'])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X23 @ X22)
% 0.46/0.65          | ((k1_relat_1 @ X23) = (X22))
% 0.46/0.65          | ~ (v4_relat_1 @ X23 @ X22)
% 0.46/0.65          | ~ (v1_relat_1 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.46/0.65         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.65  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('96', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['95', '96'])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['93', '94', '97'])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['77', '88'])).
% 0.46/0.65  thf('100', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.65       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['36'])).
% 0.46/0.65  thf('102', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['100', '101'])).
% 0.46/0.65  thf('103', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['37', '102'])).
% 0.46/0.65  thf('104', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['35', '103'])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '104'])).
% 0.46/0.65  thf('106', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 0.46/0.65            = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.46/0.65  thf('107', plain,
% 0.46/0.65      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B))
% 0.46/0.65         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['105', '106'])).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.46/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.65  thf('111', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['35', '103'])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['110', '111'])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['107', '112'])).
% 0.46/0.65  thf('114', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('115', plain,
% 0.46/0.65      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.65  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('118', plain,
% 0.46/0.65      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.65  thf('119', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['35', '103'])).
% 0.46/0.65  thf('120', plain,
% 0.46/0.65      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.65  thf('121', plain,
% 0.46/0.65      (![X24 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('122', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('123', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.65          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.65          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.65          | ~ (v1_funct_1 @ X19)
% 0.46/0.65          | (v1_xboole_0 @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.65  thf('124', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.65  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('127', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X23 @ X22)
% 0.46/0.65          | ((k1_relat_1 @ X23) = (X22))
% 0.46/0.65          | ~ (v4_relat_1 @ X23 @ X22)
% 0.46/0.65          | ~ (v1_relat_1 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.65  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('131', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('133', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['131', '132'])).
% 0.46/0.65  thf('134', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['129', '130', '133'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('136', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.65  thf('137', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['121', '136'])).
% 0.46/0.65  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('139', plain,
% 0.46/0.65      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['137', '138'])).
% 0.46/0.65  thf('140', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['37', '102'])).
% 0.46/0.65  thf('141', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['139', '140'])).
% 0.46/0.65  thf('142', plain,
% 0.46/0.65      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.65         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['120', '141'])).
% 0.46/0.65  thf('143', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['113', '142'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
